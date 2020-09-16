import unittest
from math import inf
from subprocess import run, PIPE

PART1_MODELS = [('texas.ifetch1^5.E', 19),
                ('vis.eisenberg.E', 19),
                ('texas.two_proc^1.E', 13),
                ('texas.two_proc^2.E', 14),
                ('texas.two_proc^5.E', 13),
                ('cmu.gigamax.B', inf)]

PART2_MODELS = [('nusmv.syncarb5^2.B', inf),
                ('vis.emodel.E', inf),
                ('cmu.gigamax.B', inf),
                ('ken.flash^13.C', inf),
                ('nusmv.syncarb10^2.B', inf),
                ('texas.ifetch1^8.E', 3)]


def get_output(boolean):
    if boolean:
        return 'OK'
    else:
        return 'FAIL'


class BmcTestCase(unittest.TestCase):
    def test_part1(self):
        for model_name, safe_bound in PART1_MODELS:
            print(f'testing part1 for {model_name} ...')
            bounds = set([2 ** i for i in range(8)])
            if safe_bound != inf:
                bounds = bounds.union({safe_bound, safe_bound + 1})
            for bound in bounds:
                script_output = run(f'./run-part1.sh ../models/{model_name}.aag {bound}', cwd='../scripts', shell=True, stdout=PIPE).stdout.decode('utf-8').strip()
                expected_output = get_output(bound <= safe_bound)
                self.assertEqual(script_output, expected_output)

    def test_part2(self):
        for model_name, safe_bound in PART2_MODELS:
            print(f'testing part2 for {model_name} ...')
            script_output = run(f'./run-part2.sh ../models/{model_name}.aag', cwd='../scripts', shell=True, stdout=PIPE).stdout.decode('utf-8').strip()
            expected_output = get_output(safe_bound == inf)
            self.assertEqual(script_output, expected_output)


if __name__ == '__main__':
    unittest.main()
