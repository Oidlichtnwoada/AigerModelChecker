from subprocess import run, PIPE
from sys import argv

from aiger_parser import Parser, Node
from dimacs_generator import Generator


class BoundedModelChecker:
    def __init__(self, filename, bound, interpolation):
        with open(f'../models/{filename}.aag') as file:
            self.aiger = file.read()
        parser = Parser(self.aiger, bound)
        self.model = parser.parse()
        generator = Generator(self.model, bound)
        if not interpolation:
            generator.generate_bounded()
            output = run(['../minisat/core/minisat_core', '../dimacs/dimacs.txt'], stdout=PIPE).stdout.decode('ascii')
            if 'UNSATISFIABLE' in output:
                print('OK')
            else:
                print('FAIL')
        else:
            states_formula = generator.initial()
            safety_formula = generator.safety()
            equivalences_formula = generator.equivalences()
            while True:
                current_formula = Node.And(states_formula, Node.And(safety_formula, equivalences_formula))
                generator.generate_dimacs(current_formula)
                output = run(['../minisat_proof/minisat_proof', '-c', '../dimacs/dimacs.txt'], stdout=PIPE).stdout.decode('ascii')
                if 'UNSATISFIABLE' in output:
                    proof_tree = generator.generate_proof_tree(output)
                    next_states_formula = generator.compute_next_states_formula(states_formula, proof_tree)
                    if next_states_formula.equals(states_formula):
                        print('OK')
                        break
                    else:
                        states_formula = next_states_formula
                else:
                    print('FAIL')
                    break


BoundedModelChecker(argv[1], int(argv[2]), bool(int(argv[3])))
