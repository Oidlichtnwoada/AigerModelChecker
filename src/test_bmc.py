import unittest
from subprocess import run, PIPE


class BmcTestCase(unittest.TestCase):
    def test_bmc(self):
        script_output = run('./example.sh', cwd='../scripts', shell=True, stdout=PIPE).stdout.decode('utf-8')
        expected_output = 'OK\nFAIL\nOK\nFAIL\nOK\nFAIL\nOK\nOK\n'
        self.assertEqual(script_output, expected_output)


if __name__ == '__main__':
    unittest.main()
