from subprocess import run, PIPE
from sys import argv

from aiger_parser import Parser, Node
from dimacs_generator import Generator


# definition of the bmc object which executes the checking routines
class BoundedModelChecker:
    def __init__(self, filename, bound, interpolation, debug=False):
        with open(filename) as file:
            self.aiger = file.read()
        self.bound = bound
        self.interpolation = interpolation
        self.debug = debug

    # start the bmc in interpolation or bounded model checking mode
    def start(self):
        if self.interpolation:
            if self.debug:
                print(','.join(['bound', 'proof_tree_size', 'proof_tree_steps', 'interpolant_size', 'interpolants_equal_size']))
            self.start_interpolation(out=True)
        else:
            assert self.bound >= 0
            self.start_bmc(self.bound, out=True)

    # start the bmc routine and print if the model is save for the current bound
    def start_bmc(self, bound, out=False):
        parser = Parser(self.aiger, bound)
        model = parser.parse()
        generator = Generator(model, bound)
        generator.generate_bounded_model_checking_dimacs()
        output = run(['../minisat/core/minisat_core', '../dimacs/dimacs.txt'], stdout=PIPE).stdout.decode('utf-8')
        if 'UNSATISFIABLE' in output:
            if out:
                print('OK')
            return True
        else:
            if out:
                print('FAIL')
            return False

    # start the interpolation routine and print if the model is save
    def start_interpolation(self, out=False):
        # start with small bound
        current_bound = 1
        while True:
            # check if model is safe within the current bound
            if self.start_bmc(current_bound):
                # if the model is safe within the current bound then create relevant formulas
                parser = Parser(self.aiger, current_bound)
                model = parser.parse()
                generator = Generator(model, current_bound)
                initial_formula = generator.initial()
                first_equivalences_formula = generator.equivalences(0, 1)
                second_equivalences_formula = generator.equivalences(2, current_bound)
                first_transition_formula = generator.transition(0, 0)
                second_transition_formula = generator.transition(1, current_bound - 1)
                safety_formula = generator.safety(current_bound, current_bound)
                current_interpolant = Node.false(model)
                while True:
                    # build the two clause sets and compute the interpolant if possible
                    first_formula = Node.and_formula(first_equivalences_formula, initial_formula, first_transition_formula)
                    first_clauses = generator.generate_clauses(first_formula)
                    second_formula = Node.and_formula(second_equivalences_formula, safety_formula, second_transition_formula)
                    second_clauses = generator.generate_clauses(second_formula)
                    generator.build_dimacs(first_clauses.union(second_clauses))
                    output = run(['../minisat_proof/minisat_proof', '-c', '../dimacs/dimacs.txt'], stdout=PIPE).stdout.decode('utf-8')
                    if 'UNSATISFIABLE' in output:
                        # compute interpolant from the unsatisfiability proof
                        proof_tree = generator.generate_proof_tree(output)
                        next_interpolant = generator.compute_interpolant(first_clauses, second_clauses, proof_tree)
                        interpolants_not_equal_formula = Node.not_equal(current_interpolant, next_interpolant)
                        if self.debug:
                            print(','.join([str(current_bound), str(len(proof_tree)), str(Generator.get_proof_tree_steps((), proof_tree)),
                                            str(next_interpolant.count_nodes_in_formula()), str(interpolants_not_equal_formula.count_nodes_in_formula())]))
                        generator.build_dimacs(generator.generate_clauses(interpolants_not_equal_formula))
                        output = run(['../minisat/core/minisat_core', '../dimacs/dimacs.txt'], stdout=PIPE).stdout.decode('utf-8')
                        if 'UNSATISFIABLE' in output:
                            # interpolant computation has converged
                            if out:
                                print('OK')
                            return True
                        else:
                            # interpolant added new information to the initial state - compute new interpolant
                            initial_formula = Node.or_formula(initial_formula, next_interpolant)
                            current_interpolant = next_interpolant
                    else:
                        # possible satisfiability due to an overapproximation of reachable states in the interpolant - increase bound and try again
                        current_bound += 1
                        break
            else:
                # report FAIL if the model is not safe within the current bound
                if out:
                    print('FAIL')
                return False


BoundedModelChecker(argv[1], int(argv[2]), bool(int(argv[3])), debug=bool(int(argv[4]))).start()
