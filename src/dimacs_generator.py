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
        # preprocess the model to use literal objects
        self.preprocess()
        # build syntax tree of formula to check
        formula = Node(NodeType.AND, self.initial(), Node(NodeType.AND, self.transition(), self.safety()))
        # remove constants from formula
        self.remove_constants(formula)
        clauses = self.generate_clauses(formula)
        self.build_dimacs(clauses)

    # convert a single literal string to a literal object
    @staticmethod
    def convert_to_literal_object(literal):
        sign = -1 if bool(literal % 2) else 1
        # add 1 because constants were added at index 1
        index = (literal // 2) + 1
        return Node(NodeType.LITERAL, None, None, index * sign)

    # change the list structure to hash maps to speed up searching
    def preprocess(self):
        inputs = {}
        for index, inp in enumerate(self.model.inputs):
            inputs[index] = self.convert_to_literal_object(inp)
        self.model.inputs = inputs
        latches = {}
        for out, inp in self.model.latches:
            latches[self.convert_to_literal_object(out)] = self.convert_to_literal_object(inp)
        self.model.latches = latches
        outputs = {}
        for index, out in enumerate(self.model.outputs):
            outputs[index] = self.convert_to_literal_object(out)
        self.model.outputs = outputs
        and_gates = {}
        for out, inp_0, inp_1 in self.model.and_gates:
            and_gates[self.convert_to_literal_object(out)] = (self.convert_to_literal_object(inp_0), self.convert_to_literal_object(inp_1))
        self.model.and_gates = and_gates
        self.model.positive_allowed_literals = set(list(self.model.inputs.values()) + list(self.model.latches.keys()) + Node.get_constants())
        self.model.negative_allowed_literals = set([x.get_negated_copy() for x in self.model.positive_allowed_literals])
        self.model.allowed_literals = self.model.positive_allowed_literals.union(self.model.negative_allowed_literals)
        # add 1 because constants were added at index 1
        self.model.maximum_variable_index += 1
        self.model.label_start_index = self.model.maximum_variable_index * (self.bound + 1)
        self.model.label_running_index = self.model.label_start_index

    # build equivalence out of OR, AND and NEGATION
    @staticmethod
    def get_equivalence_formula(arg_0, arg_1):
        neg_arg_0 = arg_0.get_negated_copy()
        neg_arg_1 = arg_1.get_negated_copy()
        return Node(NodeType.OR, Node(NodeType.AND, arg_0, arg_1), Node(NodeType.AND, neg_arg_0, neg_arg_1))

    # build up the initial state formula to guarantee that all latches are initialized to zero
    def initial(self):
        formula = Node.true()
        for out in self.model.latches:
            formula = Node(NodeType.AND, formula, out.get_negated_copy())
        return formula

    # build up the safety formula which is satisfiable if a bad state has been reached
    def safety(self):
        formula = Node.false()
        out = self.model.outputs[0]
        for i in range(self.bound + 1):
            current_step_out = self.replace_with_allowed_literals(out.get_copy())
            self.increment_steps(current_step_out, i)
            formula = Node(NodeType.OR, formula, current_step_out)
        return formula

    # increments the steps of literals in a formula
    def increment_steps(self, formula, steps):
        if formula.node_type == NodeType.LITERAL:
            literal = formula
            if literal not in Node.get_constants():
                value = self.model.maximum_variable_index * steps
                if literal.label < 0:
                    literal.label -= value
                else:
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
            formula = Node(NodeType.AND, formula, transition_step)
        return formula

    # build up the transition step formula from step 0 to 1
    def transition_formula(self):
        formula = Node.true()
        for out in self.model.latches:
            next_step_out = out.get_copy()
            self.increment_steps(next_step_out, 1)
            prev_step_in = self.replace_with_allowed_literals(self.model.latches[out].get_copy())
            transition = self.get_equivalence_formula(next_step_out, prev_step_in)
            formula = Node(NodeType.AND, formula, transition)
        return formula

    # only the inputs of the system, outputs of latches and constants occur in the returned formula and their negations
    def replace_with_allowed_literals(self, formula):
        formula = Node(NodeType.AND, Node.true(), formula)
        while True:
            unallowed_literals = []
            self.find_literals_in_formula(formula, self.model.allowed_literals, False, unallowed_literals)
            if len(unallowed_literals) == 0:
                break
            else:
                for unallowed_literal, first_argument in unallowed_literals:
                    if unallowed_literal in self.model.and_gates:
                        inp_0, inp_1 = map(Node.get_copy, self.model.and_gates[unallowed_literal])
                        replacement_formula = Node(NodeType.AND, inp_0, inp_1)
                    else:
                        inp_0, inp_1 = map(Node.get_copy, self.model.and_gates[unallowed_literal.get_negated_copy()])
                        replacement_formula = Node(NodeType.AND, inp_0, inp_1).get_negated_copy()
                    replacement_formula.parent = unallowed_literal.parent
                    if first_argument:
                        replacement_formula.parent.first_argument = replacement_formula
                    else:
                        replacement_formula.parent.second_argument = replacement_formula
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
                        if constant.parent.node_type == NodeType.AND:
                            replacement_formula = constant.parent.second_argument if first_argument else constant.parent.first_argument
                        elif constant.parent.node_type == NodeType.OR:
                            replacement_formula = Node.true()
                    elif constant == Node.false():
                        if constant.parent.node_type == NodeType.AND:
                            replacement_formula = Node.false()
                        elif constant.parent.node_type == NodeType.OR:
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

    # find constants in a formula
    def find_literals_in_formula(self, formula, literals, included, container, first_argument=True):
        if formula.node_type == NodeType.LITERAL:
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
        if formula.node_type == NodeType.LITERAL:
            if formula == Node.false():
                return {('-1',), ('1',)}
            elif formula == Node.true():
                return {('1',)}
        else:
            self.add_labels(formula)
            clauses = {(formula.label.label,)}
            self.add_equivalences(formula, clauses)
            return clauses

    # generate the dimacs string
    def build_dimacs(self, clauses):
        with open('../dimacs/dimacs.txt', 'w') as file:
            file.write(f'p cnf {self.model.label_running_index} {len(clauses)}\n')
            [file.write(f'{" ".join(map(str, clause))} 0\n') for clause in clauses]

    # label all internal nodes in the syntax tree of the formula
    def add_labels(self, formula):
        if formula.node_type == NodeType.LITERAL:
            return
        else:
            self.model.label_running_index += 1
            formula.label = Node(NodeType.LITERAL, None, None, self.model.label_running_index)
            self.add_labels(formula.first_argument)
            self.add_labels(formula.second_argument)

    # generate clauses for all the equivalences used in the Tseitin transformation
    def add_equivalences(self, formula, clauses):
        if formula.node_type == NodeType.LITERAL:
            return
        else:
            label = formula.label.label
            first_argument = formula.first_argument
            if first_argument.node_type != NodeType.LITERAL:
                first_argument = first_argument.label.label
            else:
                first_argument = first_argument.label
            second_argument = formula.second_argument
            if second_argument.node_type != NodeType.LITERAL:
                second_argument = second_argument.label.label
            else:
                second_argument = second_argument.label
            if formula.node_type == NodeType.AND:
                sign = -1
            else:
                sign = 1
            clauses.add((label * -1 * sign, first_argument * sign, second_argument * sign))
            clauses.add((label * sign, first_argument * -1 * sign))
            clauses.add((label * sign, second_argument * -1 * sign))
            self.add_equivalences(formula.first_argument, clauses)
            self.add_equivalences(formula.second_argument, clauses)

    # count the nodes in a formula
    def count_nodes_in_formula(self, formula):
        if formula.node_type == NodeType.LITERAL:
            return 1
        else:
            return self.count_nodes_in_formula(formula.first_argument) + self.count_nodes_in_formula(formula.second_argument)


class Node:
    def __init__(self, node_type, first_argument, second_argument, label=0, parent=None):
        self.node_type = node_type
        self.first_argument = first_argument
        if self.first_argument:
            self.first_argument.parent = self
        self.second_argument = second_argument
        if self.second_argument:
            self.second_argument.parent = self
        self.label = label
        self.parent = parent

    def get_negated_copy(self):
        if self.node_type == NodeType.AND:
            return Node(NodeType.OR, self.first_argument.get_negated_copy(), self.second_argument.get_negated_copy(), self.label, self.parent)
        elif self.node_type == NodeType.OR:
            return Node(NodeType.AND, self.first_argument.get_negated_copy(), self.second_argument.get_negated_copy(), self.label, self.parent)
        elif self.node_type == NodeType.LITERAL:
            return Node(NodeType.LITERAL, self.first_argument, self.second_argument, self.label * -1, self.parent)

    def get_copy(self):
        if self.node_type == NodeType.AND:
            return Node(NodeType.AND, self.first_argument.get_copy(), self.second_argument.get_copy(), self.label, self.parent)
        elif self.node_type == NodeType.OR:
            return Node(NodeType.OR, self.first_argument.get_copy(), self.second_argument.get_copy(), self.label, self.parent)
        elif self.node_type == NodeType.LITERAL:
            return Node(NodeType.LITERAL, self.first_argument, self.second_argument, self.label, self.parent)

    def __eq__(self, other):
        return self.label == other.label

    def __hash__(self):
        return self.label

    @staticmethod
    def true():
        return Node(NodeType.LITERAL, None, None, -1)

    @staticmethod
    def false():
        return Node(NodeType.LITERAL, None, None, 1)

    @staticmethod
    def get_constants():
        return [Node.true(), Node.false()]
