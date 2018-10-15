(*applica in pipe le funzioni f(x)=x+1 e g(y)=y*2 all'intero 8*)
sem (Appl(Pipe(Seq(Fun("x",Sum(Den("x"),Eint(1))),Seq(Fun("y",Prod(Den("y"),Eint(2))),Nil))),Eint(8))) (emptyenv Unbound);;

(*applica tre volte la funzione f(x)=x^2 a 2*)
sem (Appl(ManyTimes(3,Fun("x",Prod(Den("x"),Den("x")))),Eint(2))) (emptyenv Unbound);;

(*dichiara la funzione f(x)=[(x+x),(x*4)] e la applica all'intero 9*)
sem (Let("f",Fun("x",ETup(Seq(Sum(Den("x"),Den("x")),Seq(Prod(Den("x"),Eint(4)),Nil)))),Appl(Den("f"),Eint(9)))) (emptyenv Unbound);;

(*ancora pipe: il body della funzione più esterna è una tupla*)
sem (Appl(Pipe(Seq(Fun("x",ETup(Seq(Sum(Den("x"),Den("x")),Seq(Prod(Den("x"),Eint(4)),Nil)))),Seq(Fun("y",Sum(Den("y"),Eint(3))),Nil))),Eint(1))) (emptyenv Unbound);;

(*manytimes su espressione Ebool: genera errore*)
sem (Appl(ManyTimes(3,Ebool(true)),Ebool(false))) (emptyenv Unbound);;

(*ricorsione con pipe*)
sem (Let("g",Pipe(Seq(Fun("x",Sum(Den("x"),Eint(1))),Seq(Fun("y",Prod(Den("y"),Eint(2))),Nil))),
	Letrec("f","n",Ifthenelse(Eq(Den("n"),Eint(0)),Eint(0),Appl(Den("g"),Sum(Eint(1),(Appl(Den("f"),Diff(Den("n"),Eint(1))))))),Appl(Den("f"),Eint(3))))) (emptyenv Unbound);;

(*tupla di tuple*)
sem (ETup(Seq(ETup(Seq(Ebool(true),Nil)),Seq(ETup(Seq(Eint(8),Nil)),Nil)))) (emptyenv Unbound);;

(*record*)
sem (Rec([("x",Eint(9));("y",Sum(Eint(2),Eint(3)))])) (emptyenv Unbound);;
