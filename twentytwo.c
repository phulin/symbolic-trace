int main(int argc, char *argv[]) {
	int input = (argv[1][1] - '0') * 10 + (argv[1][0] - '0');
	if (input == 22)
		return 42;
	else
		return 32;
}
