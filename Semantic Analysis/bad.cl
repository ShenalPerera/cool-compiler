class Main inherits IO{

	x: Int;
	y: String;
	f: Foo;

	z Bool;

	main(): Object {{

		x <- 10; x <- 31; y <- 10; f <- new Foo;

		isvoid true; isvoid false; void x;

		let x:Int <- 5 in x;
      	}};

 	foo(): String {"Hello Compilers"};

	a : A;
    	b : B;
};

class Foo {
 	x:Int <- 3
};

class A {
	foo:Int;
	main() : Int { 6 };
};

class B inherits A {
	bar:Int;
};

C {
	func():Int { { self; "hello world"; true; 1; } };
};
