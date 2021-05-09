---
title: "STL in C++"
category: "General"
date: "2021-05-09 12:00:00 +09:00"
desc: "STL Implementations in C++"
thumbnail: "./images/cpp_stl/scoreboard.png"
alt: "markdown logo"
---

```md
Q> Implement linear search function using templates in C++ to work on all data types.
---
```


```cpp

#include <iostream>

using namespace std;

//Linear search

template<typename T> //This search function will function for all possible data types
int search(T arr[], int n, T key){
	for(int p =0; p<n; p++){
		if(a[p] == key)
		{ return p; }
	}
return n; //if element not found, return the (last-1) index
}


int main()
{
 int a[] = {1,2,3,4,10,12};
 int n = sizeof(a)/sizeof(int);
 int key = 10;
 cout << search(a,n,key) << endl; //index position = 4
 

 float b[] = {1.1, 1.2, 1.3};
 float k = 1.2;
 cout << search(b, 3, k}<< endl; //index position = 1


return 0;

}

```

```md
Q> What are containers in STL. Why should we bother about them?
---
```


```
Containers are specialised data structures in C++ which has optimised utility functions implemented within them to manipulate and make use of them
We should use them because we don't want to reinvent the cycle
We should use them for reusability and scalability


Types

- Sequence containers: data structures which can be accessed sequentially
ex., vector, list, deque(double ended queue), arrays, forward list

- Container adaptors: provides different interface for sequential containers
ex., queue, priority, stack

- Associative containers: already sorted data structures that can be quickly searched (Ologn complexity)
ex., set, multiset, map, multimap

- Unordered associative containers: unordered/unsorted data structure like lookup table or hashmap where searching is done using 
(key,value) pair
ex., unordered_set, unordered_multiset, unordered_map, unordered_multimap
```



```md
Q> What are iterators.
---
```

```
Iterators as an entity helps us to access the data within a container with certain restrictions

Types(most common)

-Forward iterators
-Bidirectional iterators
-Random access iterators
```
```md
Q> Write a generic template linear search function using containers and iterators which will work for different datatypes as well as different containers
---
```

```cpp
#include<iostream>
#include<list>

template <class ForwardIterator, class T>
ForwardIterator search(ForwardIterator start, ForwardIterator end, T key){
	
	while(start!=end){
		if(*start==key){return start;}
	}
	start++;
}
return end;
}


int main()
{
 list<int> l;
 l.push_back(1);
 l.push_back(2);
 l.push_back(5);
 l.push_back(3);

 auto it = search(l.begin(), l.end(), 5);
 //"l.begin()" datatype will be "list<int>::iterator" which is equal to ForwardIterator  

 cout << *it << endl;
}
```

```md
Q> Do you find any similarities of these with UVM?
---
```
```
Yes UVM also implements base template classes and proxy classes and their base utility functions like copy, clone, convert2string and many others which are generic, can be used easily, manipulated and expanded to a large scale
```

```md
Q> Write a function class/comparator class to search a book object within a list of book objects
---
- Book object/class contains name and price as member items.
- In order to compare two book objects you need to compare both of their name as well as price. If both are same then the 2 objects are same otherwise not
```

```cpp
#include<iostream>
#include<list>
#include<string>


//class that can compare two Book classes 

class BookCompare{  
/**************** 
BookCompare cmp;
cmp(); // it is an object and also automatically calls operator function because "()" is overloaded
//So it also called functional object or functor
****************/


public:
	bool operator()(Book A, Book B){
		if(A.name == B.name && A.price == B.price){return true;}
	}
	return false;
};

//Class Book itself

class Book{
	public:
		string name;
		int price;
	Book(){//default constructor
	}
	Book(string name, int price){//parameterized constructor 
		this->name = name;
		this->price = price;
	}
};


int main(){

	Book b1("C++", 120);
	Book b2("python", 100);
	Book b3("system verilog", 125);

	list<Book> l; //list of book objects
	l.push_back(b1);
	l.push_back(b2);
	l.push_back(b3);
	
	Book booktofind("system verilog", 125);
	BookCompare cmp;
	if(cmp(b3,booktofind)){ cout<<"Same books"<<endl; }
}

```

```md
Q> Make use of generic template containers, iterators and comparator classes to implement the above solution
---
```
```cpp

#include<iostream>
#include<list>
#include<string>
#include<vector>

template <class ForwardIterator, class T, class Compare>
ForwardIterator search(ForwardIterator start, ForwardIterator end, T key, Compare cmp){
	
	while(start!=end){
		if(cmp(*start,key)){return start;}
	}
	start++;
}
return end;
}

//Class Book itself

class Book{
	public:
		string name;
		int price;
	Book(){//default constructor
	}
	Book(string name, int price){//parameterized constructor 
		this->name = name;
		this->price = price;
	}
};


int main(){

	Book b1("C++", 120);
	Book b2("python", "100");
	Book b3("system verilog", "125");

	list<Book> l; //list of book objects
	l.push_back(b1);
	l.push_back(b2);
	l.push_back(b3);
	
	Book booktofind("system verilog", 125);
	BookCompare cmp;
	auto it = search(l.begin(), l.end(), booktofind, cmp);
        if(it!=l.end()){ cout <<"Book found in list"<< endl; }
}

```

```md
Q> Use the STL find function to find an element in an array
---
```

```cpp
#include<iostream>
#include<algorithm> //This is the main header file you need in life!

using namespace std;

int main(){
	int arr[] = {1,10,11,9,100};
	int n = sizeof(arr)/sizeof(int);
	//Search --> find
	int key = 11; //need to find 11
	auto it = find(arr, arr+n, key); //arr+n is last element address
        cout << it - arr << endl; //because "find" returns address of index so you need to subtract base address
        //i.e., arr
        
	if(it-arr==n){ cout << key << "not present" << endl;}
	else { cout << key << "present at" << it - arr << endl;  }
	return 0;
}

```

```md
Q> Use the STL binary_search (Complexity- logn if array is sorted) function to find an element in an array
---
```

```cpp
#include<iostream>
#include<algorithm> //This is the main header file you need in life!

using namespace std;

int main(){
	int arr[] = {1, 9, 10, 11, 100};
	int n = sizeof(arr)/sizeof(int);
	//Search --> find
	int key = 11; //need to find 11
	bool present = binary_search(arr, arr+n, key); //arr+n is last element address
    
	
	if(present){ cout << key << "present" << endl;}
	else { cout << key << "Not present" << endl;  }


	auto it = lower_bound(arr,arr+n,11); //>=key
	cout<<(it-arr)<<endl; //so index=3

	cout << "Occ Freq of 11 is"<< (upper_bound(arr,arr+n,11)-lower_bound(arr,arr+n,11)) <<endl; //Only 1 time
	return 0;
}

```

```md
Q> Use the STL sort function to sort an array
---
```
```cpp
#include <iostream>
#include <algorithm>
using namespace std;

int main(){

	int n, key;
	cin >> n; //take no of elements as i/p

	int arr[1000];

	for(int i = 0; i < n; i++){
		cin >> arr[i];
	}

	sort(arr, arr+n);

    //Print the sorted array
	for (int i = 0; i < n; i++ ){
		cout <<arr[i] << ",";
	}



	return 0;
}
```

```md
Q> Use the STL sort function to sort an array in descending order
---
```

```cpp
#include <iostream>
#include <algorithm>
using namespace std;
//Define a comparator function
bool compare(int a, int b){ return a > b; } //return true when a>b 

int main(){

	int n, key;
	cin >> n; //take no of elements as i/p

	int arr[1000];

	for(int i = 0; i < n; i++){
		cin >> arr[i];
	}

	sort(arr, arr+n, compare); //pass comparator function as parameter to template sort function

    //Print the sorted array
	for (int i = 0; i < n; i++ ){
		cout <<arr[i] << ",";
	}



	return 0;
}
```

```md
Q> Use your own bubble sort function that takes another comparator function as parameter to sort an array in descending order
---
```

```cpp
#include <iostream>
#include <algorithm>
using namespace std;
//Define a comparator function
bool compare(int a, int b){ return a < b; } //return true when a>b 

void bubble_sort(int arr[], int n, bool (&cmp) (int a, int b) ){
	for(int i = 1; i <= n-1; i++){
		for(int j = 0; j <= n-i-1; j++){
			if(cmp(arr[j], arr[j+1]){
				swap(a[j], a[j+1]);
			}
		}
	}
}



int main(){

	int n, key;
	cin >> n; //take no of elements as i/p

	int arr[1000];

	for(int i = 0; i < n; i++){
		cin >> arr[i];
	}

	bubble_sort(arr, arr+n, compare); //pass comparator function as parameter to template sort function

    //Print the sorted array
	for (int i = 0; i < n; i++ ){
		cout <<arr[i] << ",";
	}



	return 0;
}
```

