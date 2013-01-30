#include <stdio.h>

int main(int argc, char **argv) {
	char c = getchar();
	char cs[2];
    cs[0] = c;
cs[1] = '\0';	
	return atoi(cs);
}
