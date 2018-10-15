(*tipi algebrici*)
type ide = string;;
type exp = Eint of int | Ebool of bool | Den of ide | Prod of exp*exp | Sum of exp*exp | Diff of exp*exp |
	Eq of exp*exp | Minus of exp | IsZero of exp | Or of exp*exp | And of exp*exp | Not of exp |
	Ifthenelse of exp*exp*exp | Let of ide*exp*exp | Fun of ide*exp | Appl of exp*exp |
	Letrec of ide*ide*exp*exp | ETup of tuple | Pipe of tuple | ManyTimes of int*exp
and tuple = Nil | Seq of exp*tuple;;

(*tuple di tipo polimorfo*)
type 't tuple = VNil | VSeq of 't*'t tuple;;

(*ambiente polimorfo*)
type 't env = ide -> 't;;
let emptyenv(x) = function y -> x;;
let applyenv x y = x y;;
let bind (r : 't env) (i : ide) (v : 't) = function
	x -> if x=i then v else applyenv r x;;

(*tipi esprimibili: si aggiungono le tuple*)
type eval = Int of int | Bool of bool | FunVal of ide*exp*eval env | RecFunVal of ide*ide*exp*eval env |
	TupVal of eval tuple | Unbound;;

(*rts*)
(*eq_type e tuplecheck verificano che gli elementi di una tupla siano tutti dello stesso tipo*)
let eq_type v1 v2 = match v1 with
	Int(_) -> (match v2 with
		Int(_) -> true |
		_ -> false) |
	Bool(_) -> (match v2 with
		Bool(_) -> true |
		_ -> false) |
	FunVal(_) -> (match v2 with
		FunVal(_) -> true |
		_ -> false) |
	TupVal(_) -> (match v2 with
		TupVal(_) -> true |
	_ -> failwith("Not a valid type"));;

let rec tuplecheck (t : eval tuple) = match t with
	VNil -> true |
	VSeq(v,VNil) -> true |
	VSeq(v,VSeq(v1,t)) -> if (eq_type v v1) then tuplecheck (VSeq(v1,t))
				else failwith ("non compatible types");;

(*type checking*)
let typecheck (s : string) (v : eval) = match s with
	"int" -> (match v with
		Int(_) -> true |
		_ -> false) |
	"bool" -> (match v with
		Bool(_) -> true |
		_ -> false) |
	"tuple" -> (match v with
		TupVal(vt) -> if (tuplecheck vt) then true 
			else false |
		_ -> false) |
	_ -> failwith("not a valid type");;

(*funzioni primitive*)
let prod(x,y) = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Int(n*u))
	else failwith("Type error");;

let sum(x,y) = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Int(n+u))
	else failwith("Type error");;

let diff(x,y) = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Int(n-u))
	else failwith("Type error");;

let eq(x,y) = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Bool(n=u))
	else failwith("Type error");;

let minus x = if (typecheck "int" x) then (match x with
	Int(n) -> Int(-n))
	else failwith("Type error");;

let iszero x = if (typecheck "int" x) then (match x with
	Int(n) -> Bool(n=0))
	else failwith("Type error");;

let vel(x,y) = if (typecheck "bool" x) && (typecheck "bool" y)
	then (match (x,y) with
		(Bool(b),Bool(e)) -> (Bool(b||e)))
	else failwith("Type error");;

let et(x,y) = if (typecheck "bool" x) && (typecheck "bool" y)
	then (match (x,y) with
		(Bool(b),Bool(e)) -> Bool(b&&e))
	else failwith("Type error");;

let non(x) = if (typecheck "bool" x)
	then (match x with
		Bool(true) -> Bool(false) |
		Bool(false) -> Bool(true))
	else failwith("Type error");;

(*interprete - funzioni di supporto*)
(*build_tuple costruisce una Pipe a partire dai parametri di ManyTimes*)
let rec build_tuple (n : int) (e : exp) = if n=0 then Nil
					else Seq(e,(build_tuple (n-1) e));;

(*subst sostituisce un parametro con una espressione per comporre funzioni*)
let rec subst i e e1 = match e with
	Den(x) -> if x=i then e1 else e |
	(Eint(_) | Ebool(_)) -> e |
	IsZero(a) -> IsZero(subst i a e1) |
	Eq(a,b) -> Eq((subst i a e1),(subst i b e1)) |
	Prod(a,b) -> Prod((subst i a e1),(subst i b e1)) |
	Sum(a,b) -> Sum((subst i a e1),(subst i b e1)) |
	Diff(a,b) -> Diff((subst i a e1),(subst i b e1)) |
	Minus(a) -> Minus(subst i a e1) |
	And(a,b) -> And((subst i a e1),(subst i b e1)) |
	Or(a,b) -> Or((subst i a e1),(subst i b e1)) |
	Not(a) -> Not(subst i a e1) |
	Ifthenelse(a,b,c) -> Ifthenelse((subst i a e1),(subst i b e1),(subst i c e1)) |
	Let(x,a,b) -> Let(x,(subst i a e1),(subst i b e1)) |
	Fun(x,a) -> Fun(x,subst i a e1) |
	Appl(a,b) -> Appl((subst i a e1),(subst i b e1)) |
	Letrec(f,i,a,b) -> Letrec(f,i,(subst i a e1),b) |
	ManyTimes(n,a) -> ManyTimes(n,(subst i a e1)) |
	ETup(t) -> ETup(subst_tuple i t e1) |
	Pipe(t) -> Pipe(subst_tuple i t e1)
and subst_tuple i t e1 = match t with
	Nil -> t |
	Seq(a,t1) -> Seq((subst i a e1),(subst_tuple i t1 e1));;

(*interprete*)
let rec sem (e : exp) (r : eval env) = match e with
	Eint(n) -> Int(n) |
	Ebool(b) -> Bool(b) |
	Den(i) -> applyenv r i |
	IsZero(a) -> iszero(sem a r) |
	Eq(a, b) -> eq((sem a r),(sem b r)) |
	Prod(a, b) -> prod((sem a r), (sem b r)) |
	Sum(a, b) -> sum((sem a r), (sem b r)) |
	Diff(a, b) -> diff((sem a r), (sem b r)) |
	Minus(a) -> minus(sem a r) |
	And(a, b) -> et((sem a r), (sem b r)) |
	Or(a, b) -> vel((sem a r), (sem b r)) |
	Not(a) -> non(sem a r) |
	Ifthenelse(a, b, c) -> let g = sem a r in
		if (typecheck "bool" g) then
			(if g = Bool(true) then (sem b r) else (sem c r))
			else failwith ("nonboolean guard") |
	Let(i, e1, e2) -> (sem e2 (bind r i (sem e1 r))) |
	Fun(i, a) -> FunVal(i, a, r) |
	Appl(f, eArg) -> let fclosure = (sem f r) in
		(match fclosure with
			FunVal(arg, fbody, fDecEnv) -> (sem fbody (bind fDecEnv arg (sem eArg r))) |
			RecFunVal(f, arg, fbody, fDecEnv) -> 
				let aVal = (sem eArg r) in
					let rEnv = (bind fDecEnv f fclosure) in
						let aEnv = (bind rEnv arg aVal) in
							(sem fbody aEnv) |
			_ -> failwith("non functional value")) |
	Appl(_,_) -> failwith("no function in apply") |
	Letrec(f, i, fBody, letBody) -> let benv = bind r f (RecFunVal(f, i, fBody, r))
					in (sem letBody benv) |
	ETup(t) -> TupVal(sem_tuple t r) |
	Pipe(t) -> let t1 = sem (ETup(t)) r in
		if (typecheck "tuple" t1) then let vt = sem_tuple t r in (match vt with
			_ -> build_fun vt)
			else failwith("no tuple in pipe") |
	ManyTimes(n,e) -> let t=(build_tuple n e)
				in sem (Pipe(t)) r
and sem_tuple t (r : eval env) = match t with
	Nil -> VNil |
	Seq(e,t1) -> let v = sem e r in
			let vt = sem_tuple t1 r in if (tuplecheck vt) then VSeq(v,vt)
				else failwith("not a tuple") |
	_ -> failwith("not a tuple")
and compose v1 v2 = match v1 with
	FunVal(p,b,r) -> (match v2 with
		FunVal(p1,b1,r1) -> let b2 = (subst p b b1)
			in FunVal(p1,b2,r)) |
	_ -> failwith("no function in pipe")
and build_fun (t : eval tuple) = match t with
	VNil -> sem (Fun("x",Den("x"))) (emptyenv Unbound) |
	VSeq(v,VNil) -> v |
	VSeq(v,t1) -> compose v (build_fun t1);;
(*build_fun ha come parametro una eval tuple. Compose realizza la composizione delle funzioni presenti nella Pipe (o genera un'eccezione se i valori nella Pipe non sono funzioni)*)
