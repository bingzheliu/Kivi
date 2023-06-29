

sys_path = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, sys_path)
sys.path.insert(0, sys_path+"/kivi")

import kivi
from kivi import parser

json_config, user_defined_fss = parser.parser("../s3/from_scratch")

print(json_config, user_defined_fss)