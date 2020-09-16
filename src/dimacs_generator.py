from enum import Enum


# an enum to manage the different types of nodes used in formulas
class NodeType(Enum):
    LITERAL = 0
    AND = 1
    OR = 2
    EQUAL = 3
    NOT_EQUAL = 4


# definition of the generator object which generates formulas
class Generator:
    def __init__(self, model, bound):
        self.model = model
        self.bound = bound

    # this writes the bmc formula to the dimacs file
    def generate_bounded_model_checking_dimacs(self):
        # build expression tree of bmc formula
        formula = Node.and_formula(self.equivalences(), self.initial(), self.transition(), self.safety())
        # generate a clause set from the formula
        clauses = self.generate_clauses(formula)
        # write the clause set in dimacs style to the file
        self.build_dimacs(clauses)

    # return the formula that enforces the equivalences from the and gates
    def equivalences(self, start=None, end=None):
        if start is None:
            start = 0
        if end is None:
            end = self.bound
        equivalences = Node.true(self.model)
        for out, (inp_0, inp_1) in self.model.and_gates.items():
            equivalence = Node.equal(out.get_copy(), Node.and_formula(inp_0.get_copy(), inp_1.get_copy()))
            equivalences = Node.and_formula(equivalences, equivalence)
        all_equivalences = Node.true(self.model)
        for i in range(start, end + 1):
            current_step_equivalences = equivalences.get_copy()
            self.increment_steps(current_step_equivalences, i)
            all_equivalences = Node.and_formula(all_equivalences, current_step_equivalences)
        return all_equivalences

    # build up the initial state formula that guarantees that all latches are initialized to zero
    def initial(self):
        formula = Node.true(self.model)
        for out in self.model.latches:
            formula = Node.and_formula(formula, out.get_negated_literal_copy())
        return formula

    # build up the safety formula which is satisfiable if a bad state has been reached at any step
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
            formula = Node.or_formula(formula, current_step_bad_state_detector)
        return formula

    # build up the transition formula that connects previous step inputs to next step outputs for every latch
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
            formula = Node.and_formula(formula, transition_step)
        return formula

    # build up the transition step formula from step 0 to 1
    def transition_formula(self):
        formula = Node.true(self.model)
        for out in self.model.latches:
            next_step_out = out.get_copy()
            self.increment_steps(next_step_out, 1)
            prev_step_in = self.model.latches[out].get_copy()
            transition = Node.equal(next_step_out, prev_step_in)
            formula = Node.and_formula(formula, transition)
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

    # construct a cnf formula using tseitin transformation
    def generate_clauses(self, formula):
        # label all connectives
        self.add_labels(formula)
        # force the sat solver to pick the two constants to true and false
        clauses = {(formula.label,), (self.model.true_index,), (-self.model.false_index,)}
        processed_formulas = set()
        # transform the expression tree to clauses and add them to the set
        self.add_equivalences_to_clauses(formula, clauses, processed_formulas)
        return clauses

    # generate the dimacs file
    def build_dimacs(self, clauses):
        with open('../dimacs/dimacs.txt', 'w') as file:
            file.write(f'p cnf {self.model.label_running_index} {len(clauses)}\n')
            [file.write(f'{" ".join(map(str, clause))} 0\n') for clause in clauses]

    # label all unlabelled nodes in the syntax tree of the formula
    def add_labels(self, formula):
        if not formula.is_literal() and formula.label == 0:
            self.model.label_running_index += 1
            formula.label = self.model.label_running_index
            self.add_labels(formula.first_argument)
            self.add_labels(formula.second_argument)

    # generate clauses for all equivalences enforced by the expression tree - each formula is only processed once
    def add_equivalences_to_clauses(self, formula, clauses, processed_formulas):
        if not formula.is_literal() and formula not in processed_formulas:
            label = formula.label
            assert label != 0
            first_argument = formula.first_argument.label
            assert first_argument != 0
            second_argument = formula.second_argument.label
            assert second_argument != 0
            if formula.is_and():
                clauses.add(self.get_clause(label, first_argument * -1, second_argument * -1))
                clauses.add(self.get_clause(label * -1, first_argument))
                clauses.add(self.get_clause(label * -1, second_argument))
            elif formula.is_or():
                clauses.add(self.get_clause(label * -1, first_argument, second_argument))
                clauses.add(self.get_clause(label, first_argument * -1))
                clauses.add(self.get_clause(label, second_argument * -1))
            elif formula.is_equal():
                clauses.add(self.get_clause(label, first_argument, second_argument))
                clauses.add(self.get_clause(label * -1, first_argument * -1, second_argument))
                clauses.add(self.get_clause(label * -1, first_argument, second_argument * -1))
                clauses.add(self.get_clause(label, first_argument * -1, second_argument * -1))
            elif formula.is_not_equal():
                clauses.add(self.get_clause(label * -1, first_argument * -1, second_argument * -1))
                clauses.add(self.get_clause(label, first_argument, second_argument * -1))
                clauses.add(self.get_clause(label, first_argument * -1, second_argument))
                clauses.add(self.get_clause(label * -1, first_argument, second_argument))
            else:
                raise NotImplementedError()
            processed_formulas.add(formula)
            self.add_equivalences_to_clauses(formula.first_argument, clauses, processed_formulas)
            self.add_equivalences_to_clauses(formula.second_argument, clauses, processed_formulas)

    # compute the interpolant out of two clause sets and a proof tree
    def compute_interpolant(self, first_clauses, second_clauses, proof_tree):
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
                relevant_literals = [x for x in clause if abs(x) in second_variables]
                if len(relevant_literals) == 0:
                    label = Node.false(self.model)
                else:
                    label = Node.or_formula(*[Node.literal(literal) for literal in relevant_literals])
                    self.increment_steps(label, -1)
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
                        label = right_parent_label
                    elif right_parent_label == Node.false(self.model):
                        label = left_parent_label
                    else:
                        label = Node.or_formula(left_parent_label, right_parent_label)
                else:
                    if left_parent_label == Node.false(self.model) or right_parent_label == Node.false(self.model):
                        label = Node.false(self.model)
                    elif left_parent_label == Node.true(self.model):
                        label = right_parent_label
                    elif right_parent_label == Node.true(self.model):
                        label = left_parent_label
                    else:
                        label = Node.and_formula(left_parent_label, right_parent_label)
            labels[clause] = label

    # return a sorted clause without duplicates
    @staticmethod
    def get_clause(*labels):
        return tuple(sorted(set(labels)))

    # return the resolution steps from the root clauses to the passed clause
    @staticmethod
    def get_proof_tree_steps(clause, proof_tree):
        if len(proof_tree[clause]) == 0:
            return 0
        else:
            return 1 + Generator.get_proof_tree_steps(proof_tree[clause][0], proof_tree) + \
                   Generator.get_proof_tree_steps(proof_tree[clause][2], proof_tree)

    # generate a proof tree out of the sat solver output
    @staticmethod
    def generate_proof_tree(output):
        output = output[output.find('...') + len('...'):].strip()
        if 'Final clause: <empty>' in output:
            # ordinary case
            output = output[:output.find('Final clause: <empty>')].strip() + ' 0'
        else:
            # trivial case
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
                # add a root clause to the proof tree
                clause = Generator.get_clause(*tuple(map(int, line[line.find('ROOT') + len('ROOT'):].strip().split(' '))))
                path = ()
            else:
                # add a derived clause to the proof tree
                clause = Generator.get_clause(*tuple(map(int, line[line.find('=>') + len('=>'):].strip().split(' '))))
                path = tuple(map(int, line[line.find('CHAIN') + len('CHAIN'):line.find('=>')].replace('[', '').replace(']', '').strip().split(' ')))
                while len(path) > 3:
                    # unroll chains to get single resolution steps
                    running_clause_index += 1
                    derived_clause = Generator.get_clause(*[x for x in clauses[path[0]] + clauses[path[2]] if abs(x) != path[1]])
                    assert running_clause_index not in clauses
                    clauses[running_clause_index] = derived_clause
                    if derived_clause not in proof_tree:
                        proof_tree[derived_clause] = (clauses[path[0]], path[1], clauses[path[2]])
                    path = (running_clause_index,) + path[3:]
            clause = clause if clause != (0,) else ()
            assert number not in clauses
            clauses[number] = clause
            if clause not in proof_tree:
                proof_tree[clause] = () if path == () else (clauses[path[0]], path[1], clauses[path[2]])
        return proof_tree


# definition of the node object which builds formulas
class Node:
    def __init__(self, node_type, first_argument, second_argument, label):
        self.node_type = node_type
        self.first_argument = first_argument
        self.second_argument = second_argument
        self.label = label

    # generates a copy of the node object
    def get_copy(self):
        if self.is_literal():
            return Node.literal(self.label)
        elif self.is_and():
            return Node.and_formula(self.first_argument.get_copy(), self.second_argument.get_copy())
        elif self.is_or():
            return Node.or_formula(self.first_argument.get_copy(), self.second_argument.get_copy())
        elif self.is_equal():
            return Node.equal(self.first_argument.get_copy(), self.second_argument.get_copy())
        elif self.is_not_equal():
            return Node.not_equal(self.first_argument.get_copy(), self.second_argument.get_copy())
        else:
            raise NotImplementedError()

    # generates a negated copy of the literal object
    def get_negated_literal_copy(self):
        if self.is_literal():
            return Node.literal(self.label * -1)

    # checks if the object is a literal
    def is_literal(self):
        return self.node_type == NodeType.LITERAL

    # checks if the object is a negative literal
    def is_negative_literal(self):
        return self.is_literal() and self.label < 0

    # checks if the object is a positive literal
    def is_positive_literal(self):
        return self.is_literal() and self.label > 0

    # checks if the object is an and connective
    def is_and(self):
        return self.node_type == NodeType.AND

    # checks if the object is an or connective
    def is_or(self):
        return self.node_type == NodeType.OR

    # checks if the object is an equal connective
    def is_equal(self):
        return self.node_type == NodeType.EQUAL

    # checks if the object is a not equal connective
    def is_not_equal(self):
        return self.node_type == NodeType.NOT_EQUAL

    # equality check is done through the labels
    def __eq__(self, other):
        return self.label == other.label

    # the uniqueness in hash data structures is determined by the label
    def __hash__(self):
        return self.label

    # returns the node count of the formula object
    def count_nodes_in_formula(self):
        return 1 if self.is_literal() else 1 + self.first_argument.count_nodes_in_formula() + self.second_argument.count_nodes_in_formula()

    # returns the formula object as string
    def get_formula(self):
        if self.is_literal():
            return str(self.label)
        elif self.is_and():
            op = 'and'
        elif self.is_or():
            op = 'or'
        elif self.is_equal():
            op = 'eq'
        elif self.is_not_equal():
            op = 'neq'
        else:
            raise NotImplementedError()
        return f'({self.first_argument.get_formula()}) {op} ({self.second_argument.get_formula()})'

    # creates a literal node
    @staticmethod
    def literal(label):
        return Node(NodeType.LITERAL, None, None, label)

    # creates a literal node representing true
    @staticmethod
    def true(model):
        return Node.literal(model.true_index)

    # creates a literal node representing false
    @staticmethod
    def false(model):
        return Node.literal(model.false_index)

    # returns a literal node list representing positive and negative true and false constants
    @staticmethod
    def get_constants(model):
        return [Node.true(model), Node.false(model), Node.true(model).get_negated_literal_copy(), Node.false(model).get_negated_literal_copy()]

    # creates an and node
    @staticmethod
    def and_formula(*arguments):
        if len(arguments) == 1:
            return arguments[0]
        else:
            assert len(arguments) >= 2
            ret = Node(NodeType.AND, arguments[0], arguments[1], 0)
            for argument in arguments[2:]:
                ret = Node.and_formula(ret, argument)
            return ret

    # creates an or node
    @staticmethod
    def or_formula(*arguments):
        if len(arguments) == 1:
            return arguments[0]
        else:
            assert len(arguments) >= 2
            ret = Node(NodeType.OR, arguments[0], arguments[1], 0)
            for argument in arguments[2:]:
                ret = Node.or_formula(ret, argument)
            return ret

    # creates an equal node
    @staticmethod
    def equal(*arguments):
        assert len(arguments) >= 2
        ret = Node(NodeType.EQUAL, arguments[0], arguments[1], 0)
        for argument in arguments[2:]:
            ret = Node.equal(ret, argument)
        return ret

    # creates a not equal node
    @staticmethod
    def not_equal(*arguments):
        assert len(arguments) >= 2
        ret = Node(NodeType.NOT_EQUAL, arguments[0], arguments[1], 0)
        for argument in arguments[2:]:
            ret = Node.not_equal(ret, argument)
        return ret
