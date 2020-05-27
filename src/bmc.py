from subprocess import run, PIPE
from sys import argv

from aiger_parser import Parser
from dimacs_generator import Generator


class BoundedModelChecker:
    def __init__(self, filename, bound, interpolation):
        with open(f'../models/{filename}.aag') as file:
            self.aiger = file.read()
        parser = Parser(self.aiger)
        self.model = parser.parse()
        if not interpolation:
            generator = Generator(self.model, bound)
            generator.generate()
            output = run(['../minisat/core/minisat_core', '../dimacs/dimacs.txt'], capture_output=True).stdout.decode('ascii')
            if 'UNSATISFIABLE' in output:
                print('OK')
            else:
                print('FAIL')
        else:
            pass


BoundedModelChecker(argv[1], int(argv[2]), bool(int(argv[3])))
