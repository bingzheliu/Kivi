import sys
import os

sys_path = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, sys_path)
sys.path.insert(0, sys_path+"/kivi")

import kivi
from kivi.main import Kivi

if __name__ == '__main__':
	kivi_app = Kivi()
	kivi_app.run()