from subprocess import run, PIPE
from sys import argv, setrecursionlimit

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
            self.start_interpolation(out=True)
        else:
            self.start_bmc(self.bound, out=True)

    def start_bmc(self, bound, out=False):
        parser = Parser(self.aiger, bound)
        model = parser.parse()
        generator = Generator(model, bound)
        generator.generate_bounded_model_checking_dimacs()
        output = run(['../minisat/core/minisat_core', '../dimacs/dimacs.txt'], stdout=PIPE).stdout.decode('ascii')
        if 'UNSATISFIABLE' in output:
            if out:
                print('OK')
            return True
        else:
            if out:
                print('FAIL')
            return False

    def start_interpolation(self, out=False):
        current_bound = 10
        while True:
            if self.start_bmc(current_bound):
                parser = Parser(self.aiger, current_bound)
                model = parser.parse()
                generator = Generator(model, current_bound)
                initial_formula = generator.initial()
                first_equivalences_formula = generator.equivalences(0, 1)
                second_equivalences_formula = generator.equivalences(2, current_bound)
                first_transition_formula = generator.transition(0, 0)
                second_transition_formula = generator.transition(1, current_bound - 1)
                safety_formula = generator.safety()
                current_interpolant = Node.false(model)
                first_iteration = True
                while True:
                    first_formula = Node.And(first_equivalences_formula, Node.And(initial_formula, first_transition_formula))
                    first_clauses = generator.generate_clauses(first_formula)
                    second_formula = Node.And(second_equivalences_formula, Node.And(safety_formula, second_transition_formula))
                    second_clauses = generator.generate_clauses(second_formula)
                    generator.build_dimacs(first_clauses.union(second_clauses))
                    output = run(['../minisat_proof/minisat_proof', '-c', '../dimacs/dimacs.txt'], stdout=PIPE).stdout.decode('ascii')
                    if 'UNSATISFIABLE' in output:
                        proof_tree = generator.generate_proof_tree(output)
                        next_interpolant = generator.compute_interpolant(first_clauses, second_clauses, proof_tree)
                        interpolants_not_equal_formula = Node.get_equivalence_formula(current_interpolant, next_interpolant).get_negated_copy()
                        generator.build_dimacs(generator.generate_clauses(interpolants_not_equal_formula))
                        output = run(['../minisat/core/minisat_core', '../dimacs/dimacs.txt'], stdout=PIPE).stdout.decode('ascii')
                        if 'UNSATISFIABLE' in output and not first_iteration:
                            if out:
                                print('OK')
                            return True
                        else:
                            first_iteration = False
                            initial_formula = Node.Or(initial_formula, next_interpolant)
                            current_interpolant = next_interpolant
                    else:
                        break
            else:
                if out:
                    print('FAIL')
                return False
            current_bound += 10


setrecursionlimit(1000000000)
bmc = BoundedModelChecker(argv[1], int(argv[2]), bool(int(argv[3])))
bmc.start()
