from enum import Enum


class NodeType(Enum):
    AND = 0
    OR = 1
    LITERAL = 2


class Generator:
    def __init__(self, model, bound):
        self.model = model
        self.bound = bound

    def generate_bounded_model_checking_dimacs(self):
        # build syntax tree of formula to check
        formula = Node.And(self.equivalences(), Node.And(self.initial(), Node.And(self.transition(), self.safety())))
        # generate a clause set
        clauses = self.generate_clauses(formula)
        # write the clause set in dimacs style to a file
        self.build_dimacs(clauses)

    # add the equivalences enforced by the and gates to the formula
    def equivalences(self, start=None, end=None):
        if start is None:
            start = 0
        if end is None:
            end = self.bound
        equivalences = Node.true(self.model)
        for out, (inp_0, inp_1) in self.model.and_gates.items():
            equivalence = Node.get_equivalence_formula(out.get_copy(), Node.And(inp_0.get_copy(), inp_1.get_copy()))
            equivalences = Node.And(equivalences, equivalence)
        all_equivalences = Node.true(self.model)
        for i in range(start, end + 1):
            current_step_equivalences = equivalences.get_copy()
            self.increment_steps(current_step_equivalences, i)
            all_equivalences = Node.And(all_equivalences, current_step_equivalences)
        return all_equivalences

    # build up the initial state formula to guarantee that all latches are initialized to zero
    def initial(self):
        formula = Node.true(self.model)
        for out in self.model.latches:
            formula = Node.And(formula, out.get_negated_copy())
        return formula

    # build up the safety formula which is satisfiable if a bad state has been reached
    def safety(self, start=None, end=None):
        if start is None:
            start = 0
        if end is None:
            end = self.bound
        formula = Node.false(self.model)
        bad_state_detector = self.model.outputs[0]
        for i in range(start, end + 1):
            current_step_bad_state_detector = bad_state_detector.get_copy()
            self.increment_steps(current_step_bad_state_detector, i)
            formula = Node.Or(formula, current_step_bad_state_detector)
        return formula

    # build up the transition formula
    def transition(self, start=None, end=None):
        if start is None:
            start = 0
        if end is None:
            end = self.bound - 1
        formula = Node.true(self.model)
        transition_formula = self.transition_formula()
        for i in range(start, end + 1):
            transition_step = transition_formula.get_copy()
            self.increment_steps(transition_step, i)
            formula = Node.And(formula, transition_step)
        return formula

    # build up the transition step formula from step 0 to 1
    def transition_formula(self):
        formula = Node.true(self.model)
        for out in self.model.latches:
            next_step_out = out.get_copy()
            self.increment_steps(next_step_out, 1)
            prev_step_in = self.model.latches[out].get_copy()
            transition = Node.get_equivalence_formula(next_step_out, prev_step_in)
            formula = Node.And(formula, transition)
        return formula

    # increments the steps of literals in a formula
    def increment_steps(self, formula, steps):
        if formula.is_literal():
            literal = formula
            if literal not in Node.get_constants(self.model):
                value = self.model.maximum_variable_index * steps
                if literal.is_negative_literal():
                    literal.label -= value
                elif literal.is_positive_literal():
                    literal.label += value
        else:
            self.increment_steps(formula.first_argument, steps)
            self.increment_steps(formula.second_argument, steps)

    # construct a cnf formula using Tseitin transformation
    def generate_clauses(self, formula):
        self.add_labels(formula)
        # force SAT solver to pick the two constants to True and False
        clauses = {(formula.label,), (self.model.true_index,), (-self.model.false_index,)}
        self.add_equivalences_to_clauses(formula, clauses)
        return clauses

    # generate the dimacs file
    def build_dimacs(self, clauses):
        with open('../dimacs/dimacs.txt', 'w') as file:
            file.write(f'p cnf {self.model.label_running_index} {len(clauses)}\n')
            [file.write(f'{" ".join(map(str, clause))} 0\n') for clause in clauses]

    # label all internal nodes in the syntax tree of the formula
    def add_labels(self, formula):
        if not formula.is_literal():
            self.model.label_running_index += 1
            formula.label = self.model.label_running_index
            self.add_labels(formula.first_argument)
            self.add_labels(formula.second_argument)

    # generate clauses for all the equivalences used in the Tseitin transformation
    def add_equivalences_to_clauses(self, formula, clauses):
        if not formula.is_literal():
            label = formula.label
            first_argument = formula.first_argument.label
            second_argument = formula.second_argument.label
            factor = -1 if formula.is_and() else 1
            clauses.add(tuple({label * -1 * factor, first_argument * factor, second_argument * factor}))
            clauses.add(tuple({label * factor, first_argument * -1 * factor}))
            clauses.add(tuple({label * factor, second_argument * -1 * factor}))
            self.add_equivalences_to_clauses(formula.first_argument, clauses)
            self.add_equivalences_to_clauses(formula.second_argument, clauses)

    # compute interpolant out of two clause sets and a proof tree
    def compute_interpolant(self, first_clauses, second_clauses, proof_tree):
        first_clauses = set([tuple(sorted(x)) for x in first_clauses])
        second_clauses = set([tuple(sorted(x)) for x in second_clauses])
        first_variables = set()
        for clause in first_clauses:
            for literal in clause:
                first_variables.add(abs(literal))
        second_variables = set()
        for clause in second_clauses:
            for literal in clause:
                second_variables.add(abs(literal))
        labels = {}
        self.compute_labels((), first_clauses, second_clauses, first_variables, second_variables, proof_tree, labels)
        return labels[()]

    # compute a label of some clause in the proof_tree
    def compute_labels(self, clause, first_clauses, second_clauses, first_variables, second_variables, proof_tree, labels):
        if clause not in labels:
            if clause in first_clauses:
                label = Node.false(self.model)
                for literal in [x for x in clause if abs(x) in second_variables]:
                    literal_node = Node.Literal(literal)
                    self.increment_steps(literal_node, -1)
                    label = Node.Or(label, literal_node)
            elif clause in second_clauses:
                label = Node.true(self.model)
            else:
                resolved_on_variable = proof_tree[clause][1]
                self.compute_labels(proof_tree[clause][0], first_clauses, second_clauses, first_variables, second_variables, proof_tree, labels)
                left_parent_label = labels[proof_tree[clause][0]]
                self.compute_labels(proof_tree[clause][2], first_clauses, second_clauses, first_variables, second_variables, proof_tree, labels)
                right_parent_label = labels[proof_tree[clause][2]]
                if resolved_on_variable in first_variables and resolved_on_variable not in second_variables:
                    if left_parent_label == Node.true(self.model) or right_parent_label == Node.true(self.model):
                        label = Node.true(self.model)
                    elif left_parent_label == Node.false(self.model):
                        label = right_parent_label.get_copy()
                    elif right_parent_label == Node.false(self.model):
                        label = left_parent_label.get_copy()
                    else:
                        label = Node.Or(left_parent_label.get_copy(), right_parent_label.get_copy())
                else:
                    if left_parent_label == Node.false(self.model) or right_parent_label == Node.false(self.model):
                        label = Node.false(self.model)
                    elif left_parent_label == Node.true(self.model):
                        label = right_parent_label.get_copy()
                    elif right_parent_label == Node.true(self.model):
                        label = left_parent_label.get_copy()
                    else:
                        label = Node.And(left_parent_label.get_copy(), right_parent_label.get_copy())
            labels[clause] = label

    @staticmethod
    def get_proof_tree_size(clause, proof_tree):
        if len(proof_tree[clause]) == 0:
            return 1
        else:
            return 1 + Generator.get_proof_tree_size(proof_tree[clause][0], proof_tree) + Generator.get_proof_tree_size(proof_tree[clause][2], proof_tree)

    # generate a proof tree out of SAT solver output
    @staticmethod
    def generate_proof_tree(output):
        output = output[output.find('...') + len('...'):].strip()
        if 'Final clause: <empty>' in output:
            output = output[:output.find('Final clause: <empty>')].strip() + ' 0'
        else:
            output = output[:output.find('Trivial problem')].strip()
            line = output.count('\n')
            output = output.replace('Final clause', str(line))
            literal = abs(int(output.split()[-1]))
            first_clause = output[:output.find(f'ROOT {literal}\n')].count('\n')
            second_clause = output[:output.find(f'ROOT -{literal}\n')].count('\n')
            output = output[:output.find(f'{line}:')]
            output += f'{line}: CHAIN {first_clause} [{literal}] {second_clause} => 0'
        running_clause_index = output.count('\n')
        clauses = {}
        proof_tree = {}
        for line in output.split('\n'):
            number = int(line[:line.find(':')].strip())
            if 'ROOT' in line:
                clause = tuple(sorted(map(int, line[line.find('ROOT') + len('ROOT'):].strip().split(' '))))
                path = ()
            else:
                clause = tuple(sorted(map(int, line[line.find('=>') + len('=>'):].strip().split(' '))))
                path = tuple(map(int, line[line.find('CHAIN') + len('CHAIN'):line.find('=>')].replace('[', '').replace(']', '').strip().split(' ')))
                while len(path) > 3:
                    running_clause_index += 1
                    derived_clause = tuple(sorted(list(set([x for x in clauses[path[0]] + clauses[path[2]] if abs(x) != path[1]]))))
                    clauses[running_clause_index] = derived_clause
                    proof_tree[derived_clause] = (clauses[path[0]], path[1], clauses[path[2]])
                    path = (running_clause_index,) + path[3:]
            clause = clause if clause != (0,) else ()
            clauses[number] = clause
            proof_tree[clause] = () if path == () else (clauses[path[0]], path[1], clauses[path[2]])
        return proof_tree


# the Node object for building the syntax tree of the formula to be checked with the SAT solver
class Node:
    def __init__(self, node_type, first_argument, second_argument, label, parent):
        self.node_type = node_type
        self.first_argument = first_argument
        self.second_argument = second_argument
        self.label = label
        self.parent = parent
        if self.first_argument and self.second_argument:
            self.first_argument.parent = self
            self.second_argument.parent = self

    def get_negated_copy(self):
        if self.is_and():
            return Node.Or(self.first_argument.get_negated_copy(), self.second_argument.get_negated_copy())
        elif self.is_or():
            return Node.And(self.first_argument.get_negated_copy(), self.second_argument.get_negated_copy())
        elif self.is_literal():
            return Node.Literal(self.label * -1)

    def get_copy(self):
        if self.is_and():
            return Node.And(self.first_argument.get_copy(), self.second_argument.get_copy())
        elif self.is_or():
            return Node.Or(self.first_argument.get_copy(), self.second_argument.get_copy())
        elif self.is_literal():
            return Node.Literal(self.label)

    def is_and(self):
        return self.node_type == NodeType.AND

    def is_or(self):
        return self.node_type == NodeType.OR

    def is_literal(self):
        return self.node_type == NodeType.LITERAL

    def is_negative_literal(self):
        return self.node_type == NodeType.LITERAL and self.label < 0

    def is_positive_literal(self):
        return self.node_type == NodeType.LITERAL and self.label > 0

    def __eq__(self, other):
        return self.label == other.label

    def __hash__(self):
        return self.label

    def count_nodes_in_formula(self):
        return 1 if self.is_literal() else 1 + self.first_argument.count_nodes_in_formula() + self.second_argument.count_nodes_in_formula()

    def count_label_in_formula(self, label):
        current = int(self.label == label)
        return current if self.is_literal() else current + self.first_argument.count_label_in_formula(label) + self.second_argument.count_label_in_formula(label)

    @staticmethod
    def And(first_argument, second_argument):
        return Node(NodeType.AND, first_argument, second_argument, 0, None)

    @staticmethod
    def Or(first_argument, second_argument):
        return Node(NodeType.OR, first_argument, second_argument, 0, None)

    @staticmethod
    def Literal(label):
        return Node(NodeType.LITERAL, None, None, label, None)

    @staticmethod
    def true(model):
        return Node.Literal(model.true_index)

    @staticmethod
    def false(model):
        return Node.Literal(model.false_index)

    @staticmethod
    def get_constants(model):
        return [Node.true(model), Node.false(model), Node.true(model).get_negated_copy(), Node.false(model).get_negated_copy()]

    @staticmethod
    def get_equivalence_formula(first_argument, second_argument):
        first_argument = first_argument
        negated_first_argument = first_argument.get_negated_copy()
        second_argument = second_argument
        negated_second_argument = second_argument.get_negated_copy()
        return Node.Or(Node.And(first_argument, second_argument),
                       Node.And(negated_first_argument, negated_second_argument))
