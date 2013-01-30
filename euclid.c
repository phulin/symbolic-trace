int main(int argc, char **argv) {
	int a = (argv[1][0] - '0') * 10 + (argv[1][1] - '0');
	int b = (argv[2][0] - '0') * 10 + (argv[2][1] - '0');

	int h = (a > b) ? a : b;
	int l = (a > b) ? b : a;;
	while (l != 0) {
		h = h % l;
		int tmp = h;
		h = l;
		l = tmp;
	}
	return h;
}
