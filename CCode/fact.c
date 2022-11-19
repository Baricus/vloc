int factorial(int n) {
	int acc = 1;

	for (int i = 0; i < n; ++i) {
		acc *= (n - i);		
	}

	return acc;
}
