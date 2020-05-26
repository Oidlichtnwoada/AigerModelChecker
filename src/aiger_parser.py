from collections import deque


# structure for the model object
class Model:
    def __init__(self):
        self.maximum_variable_index = 0
        self.number_of_inputs = 0
        self.number_of_latches = 0
        self.number_of_outputs = 0
        self.number_of_and_gates = 0
        self.inputs = []
        self.latches = []
        self.outputs = []
        self.and_gates = []


class Parser:
    def __init__(self, aiger):
        self.aiger = aiger

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
        # set the inputs
        for i in range(model.number_of_inputs):
            current_line = lines.popleft()
            model.inputs.append(current_line[0])
        # set the latches
        for i in range(model.number_of_latches):
            current_line = lines.popleft()
            model.latches.append((current_line[0], current_line[1]))
        # set the outputs
        for i in range(model.number_of_outputs):
            current_line = lines.popleft()
            model.outputs.append(current_line[0])
        # set the and gates
        for i in range(model.number_of_and_gates):
            current_line = lines.popleft()
            model.and_gates.append((current_line[0], current_line[1], current_line[2]))
        return model

    def preprocess(self):
        # remove string 'aig' from the input file to allow later conversion to integers
        self.aiger = self.aiger.replace('aag', '')
        # find and remove an optional comment section
        comment_section_start_index = self.aiger.find('c\n')
        self.aiger = self.aiger if comment_section_start_index < 0 else self.aiger[:comment_section_start_index]
        # return a deque of lists of integers for every line in the input file and filter out an optional symbol table
        return deque([list(map(int, x.strip().split(' '))) for x in self.aiger.strip().split('\n') if
                      not x.strip().startswith(('i', 'l', 'o'))])
