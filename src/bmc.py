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
        if not interpolation:
            generator = Generator(self.model, bound)
            generator.generate_bounded()
            output = run(['../minisat/core/minisat_core', '../dimacs/dimacs.txt'], stdout=PIPE).stdout.decode('ascii')
            if 'UNSATISFIABLE' in output:
                print('OK')
            else:
                print('FAIL')
        else:
            generator = Generator(self.model, 1)
            equivalences_formula = generator.equivalences()
            initial_formula = generator.initial()
            transition_formula = generator.transition()
            safety_formula = generator.safety()
            current_interpolant = Node.true(self.model)
            while True:
                first_formula = Node.And(equivalences_formula, Node.And(initial_formula, transition_formula))
                first_clauses = generator.generate_clauses(first_formula)
                second_formula = Node.And(equivalences_formula, safety_formula)
                second_clauses = generator.generate_clauses(second_formula)
                all_clauses = first_clauses.union(second_clauses)
                generator.build_dimacs(all_clauses)
                output = run(['../minisat_proof/minisat_proof', '-c', '../dimacs/dimacs.txt'], stdout=PIPE).stdout.decode('ascii')
                if 'UNSATISFIABLE' in output:
                    proof_tree = generator.generate_proof_tree(output)
                    next_interpolant = generator.compute_interpolant(first_clauses, second_clauses, proof_tree)
                    if next_interpolant.equals(current_interpolant):
                        print('OK')
                        break
                    else:
                        initial_formula = Node.Or(initial_formula, next_interpolant)
                        current_interpolant = next_interpolant
                else:
                    print('FAIL')
                    break


BoundedModelChecker(argv[1], int(argv[2]), bool(int(argv[3])))
