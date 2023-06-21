import sys
import os

sys_path = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, sys_path)
sys.path.insert(0, sys_path+"/kivi")

import kivi
from kivi import verifier

if __name__ == '__main__':
	verifier.verifier()