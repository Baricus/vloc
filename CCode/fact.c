int factorial(int n) {
	int acc = 1;

	for (int i = n; i > 0; --i) {
		acc *= i;		
	}

	return acc;
}
