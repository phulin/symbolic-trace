//#include <stdio.h>

int main(int argc, char **argv) {
	float x = (argv[1][0] - '0') * 100 + (argv[1][1] - '0') * 10 + (argv[1][2] - '0');
//	printf("%f\n", (double)x);
    float xhalf = 0.5f * x;
    int i = *(int*)&x;
    i = 0x5f3759df - (i >> 1);
    x = *(float*)&i;
    x = x * (1.5f - xhalf * x * x);
//	printf("%f\n", (double)x);
    return x * 10000;
}
