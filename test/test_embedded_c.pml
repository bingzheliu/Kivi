

int i = 0;

init {


	do
	:: i < 100 ->
		c_code {
			now.i = 10;
		}
	:: else -> break;
	od;
	

}