from subprocess import run
from sys import argv

from aiger_parser import Parser
from dimacs_generator import Generator


class BoundedModelChecker:
    def __init__(self, filename, bound, interpolation):
        with open(f'./part{int(interpolation) + 1}/ascii/{filename}.aag') as file:
            self.aiger = file.read()
        parser = Parser(self.aiger)
        self.model = parser.parse()
        if not interpolation:
            generator = Generator(self.model, bound)
            self.clauses = generator.generate()
            with open('dimacs', 'w') as file:
                file.write(self.clauses)
            output = run(['./minisat/core/minisat', './dimacs'], capture_output=True).stdout.decode('ascii')
            if 'SATISFIABLE' in output:
                print('FAIL')
            else:
                print('OK')
        else:
            pass


BoundedModelChecker(argv[1], int(argv[2]), bool(int(argv[3])))
