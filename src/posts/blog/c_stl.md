---
title: "STL in C"
category: "General"
date: "2021-04-11 12:00:00 +09:00"
desc: "Some STL Implementation in C"
thumbnail: "./images/c_stl/scoreboard.png"
alt: "markdown logo"
---

```
Q1) Write an application that makes a copy of an existing text file
    It must ask the user for the source and copy file name
    Use the mechanisms provided in stdio.h
```
```cpp
Sol:
////// file_name - sol1.c ///////

#include <stdio.h>
void main()
{
	char source[100], target[100];
	
	printf("Source filename: ");
	scanf("%s", source);

	printf("Target filename: ");
	scanf("%s", target);

	FILE *source_file = fopen(source, "r");
	FILE *target_file = fopen(target, "w");

	char c = getc(source_file); //get the 1st char
	
	while(c != EOF) //Until EoF is encountered
	{
		putc(c, target_file); //write to target file
		c = getc(source_file); //get the next char
	}	

}
```
```
///////////////////////////////////////////////
//Execute command//

$	gcc –Wall -save-temps sol1.c –o sol1.out 
$	./sol1.out


//-Wall enables all compiler warning msgs
//-save-temps saves all the intermediate files in $PWD

* After Pre-processing - sol1.i
* After Compilation - sol1.s //assembly level instructions
* After Assembly - sol1.o 
* After Linking - sol1.out //executable code
```

```
/////////////////////////////////////////////////
//Source File//
//mytext.txt//

My Name is Soham!
My Name is Soham!
My Name is Soham!
My Name is Soham!
My Name is Soham!

/////////////////////////////////////////////////

/////////////////////////////////////////////////
//Target File//
//mytext.txt//

My Name is Soham!
My Name is Soham!
My Name is Soham!
My Name is Soham!
My Name is Soham!

/////////////////////////////////////////////////
```
```
Q2) Write a random number generator where uniform distribution is desired
    P(xi < RAND_MAX/2) = 0
    Use the mechanisms provided in stdlib.h
```
```md
Approach:
- Write a loop that iterates many times (100,000 to 400,000)
- The loop must generate random numbers from 1 to 1000
- Keep a count of how many are less than or equal to 500
- This count should approach 50% of the total generated numbers upto now
- P(xi <= 500) = counter/iterations
```

```cpp
Sol:
	
//////file_name - random.c//////

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <time.h>

#define TOTAL 100.0 //nos of iterations

void main()
{
	uint32_t sample;
	srand(time(0)); //current time is passed as seed to srand/random_seed function
	uint32_t i = TOTAL;
	uint32_t hits = 0; //counter
	
	while(i--) //For 100 iterations
	
	{
		sample = rand()%1000+1; //generate random numbers from 1 to 1000 excluding 0
		
		if ( sample <= 500)
			hits++; //count the number of random nos less than or equal to 500
	}
	
	printf("P(hit) = %g\n", hits/TOTAL);
}
```
```
//////
So if no. of iterations is large , it would approach 0.5 which indicates partially uniform distribution
//////

///////////////////////////////////////////////
//Execute command//

$	gcc –Wall -save-temps random.c –o random.out 
$	./random.out
///////////////////////////////////////////////
```
```
Q3) Make an application that asks for 2 strings: a sentence & a special word
    The application must print out the sentence without the special word, or report that the special word is not in the sentence
    Use the mechanisms provided in string.h
```

```cpp
Sol:

//////file_name - remove_word.c///////

#include <stdio.h>
#include <string.h>

void main()
{
	char sentence[100], word[50], temp[50];

	printf("Enter long string: ");
	scanf("%[^\n]s", sentence); //take everything except \n

	getchar(); //When user presses "enter" the discarded \n earlier has to be taken

	printf("Enter substring to remove: ");
	scanf("%[^\n]s", word); //take everything except \n

	char *str = strstr(sentence, word); //look for "word" inside "sentence" and return first occurence of common string as ptr

	if(str != NULL) //if match is found
 	{
		*str = '\0'; //assign null char to postion where str is pointing to...i.e., terminating the string "sentence" at first match position
		str += strnlen(word, 50); //move the ptr to length of the "word"
		
		//now str is pointing to remaining part of "sentence" where "word" is not present
		strncpy(temp, str, 100); //copy the remaining part in temp variable
		
		//Thus 1st part of sentence we need to print is there in sentence
		//2nd part of sentence we need to print is there in temp
		strncat( sentence, temp, 100); //concatenate part1 + part2 and store it in sentence
		
		printf("Removing the word: \"%s\"\n", sentence);

 
	}
	else
	{
		printf("\"%s\" not found in \"%s\"!\n", word, sentence);
	}
 
}
```
```
///////////////////////////////////////////////
//Execute command//

$	gcc –Wall -save-temps remove_word.c –o remove_word.out 
$	./remove_word.out
///////////////////////////////////////////////
```
```
//////output//////
//////case1///////
Enter long string: This is a nice string!
Enter substring to remove: bad
"bad" not found in "This is a nice string!"

//////case2//////
Enter long string: This is a nice string!
Enter substring to remove: nice
Removing the word: "This is a string!"

//////////////////////////////////////////////
```
```
Q4) Write the necessary code to convert a 2D point represented in Cartesian coordinates to its polar representation and the other way round
    Use the mechanisms provided in math.h
```
```md
Theory:
- cartesian coordinates = (Px,Py)
- Px = r*cos(theta)
- Py = r*sin(theta)

- Polar coordinates = (r, theta)
- r = sqrt(Px^2+Py^2)
- theta = atan2(Px,Py)
	
General formula:
- theta(radian) = theta(degrees)*{PI(radian)/180(degrees)}
- theta(degree) = theta(radian)*{180(degrees)/PI(radian)}

where PI = 22/7  
```

```cpp
Sol:


//////Ask for X and Y coordinates of point A and print out its polar representation
//////Ask for the modulus and angle(degrees) of a second point B and print out its cartesian coordinates



//////file_name - math.c///////
#include <stdio.h>
#include <math.h>

#define PI 3.14159

void main()
{
	double A_x, A_y;
	
	printf("Enter X coordinate of point A: ");
	scanf("%lf", &A_x);

	printf("Enter Y coordinate of point B: ");
	scanf("%lf", &A_y);

	double angle_in_radian = atan2(A_y, A_x);
	double angle_in_degree = angle_in_radian*(180.0/PI);

	double modulus = sqrt((A_x)^2) + ((A_y)^2));
	printf("Point A is represented in polar coordinates as (%g, %g degrees)\n\n", modulus, angle_in_degree);

///////////////////////////////////////////

	double B_radius, B_angle;
	
	printf("Enter Radius of Point B: ");
	scanf("%lf", &B_radius);

	printf("Enter Angle of Point B in degrees: ");
	scanf("%lf", &B_angle);

	double B_angle_in_radian = B_angle*(PI/180.0);
	
	double x_coordinate = B_radius*cos(B_angle_in_radian);
	double y_coordinate = B_radius*sin(B_angle_in_radian);

	printf("Point B is represented in cartesian coordinates as (%g, %g)\n\n", x_coordinate, y_coordinate);

///////////////////////////////////////////
}
```


```
///////////////////////////////////////////////
//Execute command//

$	gcc –Wall -save-temps math.c –o math.out 
$	./math.out
///////////////////////////////////////////////
```

