from enum import Enum


class NodeType(Enum):
    AND = 0
    OR = 1
    LITERAL = 2


class Generator:
    def __init__(self, model, bound):
        self.model = model
        self.bound = bound

    def generate(self):
        # build syntax tree of formula to check
        formula = Node.And(self.equivalences(), Node.And(self.initial(), Node.And(self.transition(), self.safety())))
        # remove constants from formula
        self.remove_constants(formula)
        # generate a clause set
        clauses = self.generate_clauses(formula)
        # write the clause set in dimacs style to a file
        self.build_dimacs(clauses)

    # add the equivalences enforced by the and gates to the formula
    def equivalences(self):
        formula = Node.true()
        for out, (inp_0, inp_1) in self.model.and_gates.items():
            equivalence = Node.get_equivalence_formula(out.get_copy(), Node.And(inp_0.get_copy(), inp_1.get_copy()))
            formula = Node.And(formula, equivalence)
        equivalences = Node.true()
        for i in range(self.bound + 1):
            current_step_equivalences = formula.get_copy()
            self.increment_steps(current_step_equivalences, i)
            equivalences = Node.And(equivalences, current_step_equivalences)
        return equivalences

    # build up the initial state formula to guarantee that all latches are initialized to zero
    def initial(self):
        formula = Node.true()
        for out in self.model.latches:
            formula = Node.And(formula, out.get_negated_copy())
        return formula

    # build up the safety formula which is satisfiable if a bad state has been reached
    def safety(self):
        formula = Node.false()
        initial_out = self.model.outputs[0]
        for i in range(self.bound + 1):
            current_step_out = initial_out.get_copy()
            self.increment_steps(current_step_out, i)
            formula = Node.Or(formula, current_step_out)
        return formula

    # increments the steps of literals in a formula
    def increment_steps(self, formula, steps):
        if formula.is_literal():
            literal = formula
            if literal not in Node.get_constants():
                value = self.model.maximum_variable_index * steps
                if literal.is_negative_literal():
                    literal.label -= value
                elif literal.is_positive_literal():
                    literal.label += value
        else:
            self.increment_steps(formula.first_argument, steps)
            self.increment_steps(formula.second_argument, steps)

    # build up the transition formula
    def transition(self):
        formula = Node.true()
        transition_formula = self.transition_formula()
        for i in range(self.bound):
            transition_step = transition_formula.get_copy()
            self.increment_steps(transition_step, i)
            formula = Node.And(formula, transition_step)
        return formula

    # build up the transition step formula from step 0 to 1
    def transition_formula(self):
        formula = Node.true()
        for out in self.model.latches:
            next_step_out = out.get_copy()
            self.increment_steps(next_step_out, 1)
            prev_step_in = self.model.latches[out].get_copy()
            transition = Node.get_equivalence_formula(next_step_out, prev_step_in)
            formula = Node.And(formula, transition)
        return formula

    # simplify formula by removing constants
    def remove_constants(self, formula):
        while True:
            constants = []
            self.find_literals_in_formula(formula, Node.get_constants(), True, constants)
            if len(constants) == 0:
                break
            else:
                for constant, first_argument in constants:
                    replacement_formula = None
                    if constant.parent is None:
                        break
                    if constant == Node.true():
                        if constant.parent.is_and():
                            replacement_formula = constant.parent.second_argument if first_argument else constant.parent.first_argument
                        elif constant.parent.is_or():
                            replacement_formula = Node.true()
                    elif constant == Node.false():
                        if constant.parent.is_and():
                            replacement_formula = Node.false()
                        elif constant.parent.is_or():
                            replacement_formula = constant.parent.second_argument if first_argument else constant.parent.first_argument
                    replacement_formula.parent = constant.parent.parent
                    if replacement_formula.parent is None:
                        formula = replacement_formula
                    else:
                        if replacement_formula.parent.first_argument is constant.parent:
                            replacement_formula.parent.first_argument = replacement_formula
                        else:
                            replacement_formula.parent.second_argument = replacement_formula
        return formula

    # find literals in a formula
    def find_literals_in_formula(self, formula, literals, included, container, first_argument=True):
        if formula.is_literal():
            if included:
                if formula in literals:
                    container.append((formula, first_argument))
            else:
                if formula not in literals:
                    container.append((formula, first_argument))
        else:
            self.find_literals_in_formula(formula.first_argument, literals, included, container, True)
            self.find_literals_in_formula(formula.second_argument, literals, included, container, False)

    # construct a cnf formula using Tseitin transformation
    def generate_clauses(self, formula):
        if formula.is_literal():
            if formula == Node.false():
                return {('-1',), ('1',)}
            elif formula == Node.true():
                return {('1',)}
        else:
            self.add_labels(formula)
            clauses = {(formula.label,)}
            self.add_equivalences(formula, clauses)
            return clauses

    # generate the dimacs string
    def build_dimacs(self, clauses):
        with open('../dimacs/dimacs.txt', 'w') as file:
            file.write(f'p cnf {self.model.label_running_index} {len(clauses)}\n')
            [file.write(f'{" ".join(map(str, clause))} 0\n') for clause in clauses]

    # label all internal nodes in the syntax tree of the formula
    def add_labels(self, formula):
        if formula.is_literal():
            return
        else:
            self.model.label_running_index += 1
            formula.label = self.model.label_running_index
            self.add_labels(formula.first_argument)
            self.add_labels(formula.second_argument)

    # generate clauses for all the equivalences used in the Tseitin transformation
    def add_equivalences(self, formula, clauses):
        if formula.is_literal():
            return
        else:
            label = formula.label
            first_argument = formula.first_argument.label
            second_argument = formula.second_argument.label
            if formula.is_and():
                sign = -1
            else:
                sign = 1
            clauses.add((label * -1 * sign, first_argument * sign, second_argument * sign))
            clauses.add((label * sign, first_argument * -1 * sign))
            clauses.add((label * sign, second_argument * -1 * sign))
            self.add_equivalences(formula.first_argument, clauses)
            self.add_equivalences(formula.second_argument, clauses)


# the Node object for building the formulas
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

    # count the nodes in formula
    def count_nodes_in_formula(self):
        if self.is_literal():
            return 1
        else:
            return 1 + self.first_argument.count_nodes_in_formula() + self.second_argument.count_nodes_in_formula()

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
    def true():
        return Node.Literal(-1)

    @staticmethod
    def false():
        return Node.Literal(1)

    @staticmethod
    def get_constants():
        return [Node.true(), Node.false()]

    # build equivalence formula
    @staticmethod
    def get_equivalence_formula(first_argument, second_argument):
        first_argument = first_argument.get_copy()
        negated_first_argument = first_argument.get_negated_copy()
        second_argument = second_argument.get_copy()
        negated_second_argument = second_argument.get_negated_copy()
        return Node.Or(Node.And(first_argument, second_argument),
                       Node.And(negated_first_argument, negated_second_argument))
