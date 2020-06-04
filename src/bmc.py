from subprocess import run, PIPE
from sys import argv

from aiger_parser import Parser, Node
from dimacs_generator import Generator


class BoundedModelChecker:
    def __init__(self, filename, bound, interpolation):
        with open(filename) as file:
            self.aiger = file.read()
        self.bound = bound
        self.interpolation = interpolation

    def start(self):
        if self.interpolation:
            self.start_interpolation(output=True)
        else:
            self.start_bmc(self.bound, output=True)

    def start_bmc(self, bound, output=False):
        parser = Parser(self.aiger, bound)
        model = parser.parse()
        generator = Generator(model, bound)
        generator.generate_dimacs()
        output = run(['../minisat/core/minisat_core', '../dimacs/dimacs.txt'], stdout=PIPE).stdout.decode('ascii')
        if 'UNSATISFIABLE' in output:
            if output:
                print('OK')
            return True
        else:
            if output:
                print('FAIL')
            return False

    def start_interpolation(self, output=False):
        current_bound = 1
        while True:
            if self.start_bmc(current_bound):
                parser = Parser(self.aiger, current_bound)
                model = parser.parse()
                generator = Generator(model, current_bound)
                equivalences_formula = generator.equivalences()
                initial_formula = generator.initial()
                transition_formula = generator.transition()
                safety_formula = generator.safety()
                current_interpolant = Node.false(model)
                while True:
                    first_formula = Node.And(equivalences_formula.get_copy(), Node.And(initial_formula.get_copy(), transition_formula.get_copy()))
                    first_clauses = generator.generate_clauses(first_formula)
                    second_formula = safety_formula.get_copy()
                    second_clauses = generator.generate_clauses(second_formula)
                    all_clauses = first_clauses.union(second_clauses)
                    generator.build_dimacs(all_clauses)
                    output = run(['../minisat_proof/minisat_proof', '-c', '../dimacs/dimacs.txt'], stdout=PIPE).stdout.decode('ascii')
                    if 'UNSATISFIABLE' in output:
                        proof_tree = generator.generate_proof_tree(output)
                        next_interpolant = generator.compute_interpolant(first_clauses, second_clauses, proof_tree)
                        if next_interpolant.equals(current_interpolant):
                            if output:
                                print('OK')
                            return True
                        else:
                            initial_formula = Node.Or(initial_formula, next_interpolant)
                            current_interpolant = next_interpolant
                    else:
                        break
            else:
                if output:
                    print('FAIL')
                return False
            current_bound += 1


bmc = BoundedModelChecker(argv[1], int(argv[2]), bool(int(argv[3])))
bmc.start()
