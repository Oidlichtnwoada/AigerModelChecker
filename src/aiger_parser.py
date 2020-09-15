from collections import deque

from dimacs_generator import Node


# definition the model object which is filled by the aiger file
class Model:
    def __init__(self):
        self.maximum_variable_index = 0
        self.number_of_inputs = 0
        self.number_of_latches = 0
        self.number_of_outputs = 0
        self.number_of_and_gates = 0
        self.label_running_index = 0
        self.true_index = 0
        self.false_index = 0
        self.inputs = {}
        self.latches = {}
        self.outputs = {}
        self.and_gates = {}


# definition the parser object which fills the model object
class Parser:
    def __init__(self, aiger, bound):
        self.aiger = aiger
        self.bound = bound

    # return a parsed deque from the input file content
    def preprocess(self):
        # remove string 'aig' from the input file to allow later conversion to integers
        self.aiger = self.aiger.replace('aag', '')
        # find and remove an optional comment section
        comment_section_start_index = self.aiger.find('c\n')
        self.aiger = self.aiger if comment_section_start_index < 0 else self.aiger[:comment_section_start_index]
        # create a parsed deque
        return deque([list(map(int, x.strip().split(' '))) for x in self.aiger.strip().split('\n') if
                      not x.strip().startswith(('i', 'l', 'o'))])

    # return a model filled by the contents of the parsed deque
    def parse(self):
        # preprocess the input file to a deque
        lines = self.preprocess()
        # the header is the first line in the file
        header = lines.popleft()
        # create a model and fill in the information from the header
        model = Model()
        model.maximum_variable_index = header[0]
        model.number_of_inputs = header[1]
        model.number_of_latches = header[2]
        model.number_of_outputs = header[3]
        model.number_of_and_gates = header[4]
        # set a start index for the labelling of nodes
        model.label_running_index = model.maximum_variable_index * (self.bound + 1)
        # set the indices for the two boolean constants
        model.label_running_index += 1
        model.false_index = model.label_running_index
        model.label_running_index += 1
        model.true_index = model.label_running_index
        # set the inputs
        for i in range(model.number_of_inputs):
            current_line = lines.popleft()
            model.inputs[i] = self.literal_object(current_line[0], model)
        # set the latches
        for i in range(model.number_of_latches):
            current_line = lines.popleft()
            model.latches[self.literal_object(current_line[0], model)] = self.literal_object(current_line[1], model)
        # set the outputs
        for i in range(model.number_of_outputs):
            current_line = lines.popleft()
            model.outputs[i] = self.literal_object(current_line[0], model)
        # set the and gates
        for i in range(model.number_of_and_gates):
            current_line = lines.popleft()
            model.and_gates[self.literal_object(current_line[0], model)] = \
                (self.literal_object(current_line[1], model), self.literal_object(current_line[2], model))
        return model

    # convert a single aiger literal integer to a dimacs literal object
    @staticmethod
    def literal_object(literal, model):
        if literal == 0:
            return Node.false(model)
        elif literal == 1:
            return Node.true(model)
        else:
            return Node.literal((literal // 2) * (-1 if literal % 2 else 1))
