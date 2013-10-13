(* Evaluator for a Language (c) Nathan Burgers 2013 *)

type symbol = string
datatype atom = Number of int
	      | String of string
	      | Func of symbol
datatype term = Atom of atom
	      | MonadicApp of term * atom
	      | DyadicApp of term * atom * term
infix 4 @>
datatype ('a, 'b) assoc = @> of 'a * 'b
type 'b dict = (string, 'b) assoc list

infix 9 $
fun op$ f x = f x

infix 2 o
fun opo (f,g)= fn x => f (g x)

val prelude : (real * real -> real) dict
    = [ "*" @> op*
      , "/" @> op/
      ]

type ('a, 'b) eval =
     { env : 'a dict
     , result : 'b
     }

fun id x : 'a = x
fun fst (a,b) : 'a * 'b -> 'a = a
fun snd (a,b) : 'a * 'b -> 'b = b

fun curry f a b = f (a,b)
fun uncurry f (a,b) = f a b

fun apply (f::nil) x = [f x]
  | apply (f::fs) x = (f x)::(apply fs x)

(* 'a = input type, 'b result type *)
type ('a, 'b) parser = 'a list -> ('b * ('a list)) list
fun unit v xs = [(v, xs)]
fun fail v = []
fun predicate p [] = fail p
  | predicate p (x::xs) = if p x
			  then unit x xs
			  else fail xs
fun eq x y = x = y
fun literal x = predicate (eq x)

fun one xs = literal 1 xs

infix 9 &
fun op& (f,g) = fn x => (f x, g x)

fun concat nil = nil
  | concat (x::nil) = x
  | concat (x::xs) = x @ (concat xs)

fun flatMap f xs = concat (map f xs)
infix 4 >>=
fun op>>= (f:('a,'b) parser,
	   g:'b -> ('a,'c) parser) : ('a,'c) parser
	      = fn x => flatMap (uncurry g) (f x)

fun combine c f g = f >>= (fn F => g >>= (fn G => unit (c F G)))

fun left a b = a;
fun right a b = b;
fun tuple a b = (a,b)

infix 4 ||
fun op|| (f,g) = fn x => (f x) @ (g x)

infix 4 >>
fun op>> (f,g) = f >>= (fn _ => g)

infix 4 <*>
fun op<*> (f,g) = (combine tuple) f g

infix 4 <*
fun op<* (f,g) = (combine left) f g

infix 4 *>
fun op*> (f,g) = (combine right) f g

infix 4 <=
fun op<= (p,f) = p >>= (fn a => unit (f a))

fun cons (a,b) = a::b
fun wrap a = [a]
fun many f x = ((f <= wrap) || ((f <*> many f) <= cons)) x

infix 4 <|>
fun op<|> (p,s) = (p <*> many (s *> p)) <= cons

val alpha = predicate Char.isAlpha
val digit = predicate Char.isDigit
val alphaNum = predicate Char.isAlphaNum
val whitespace = many (predicate Char.isSpace)

val word = many alpha
val integer = many digit
val decimal = many digit <* literal #"." <*> many digit

val words = word <|> whitespace

val quote = #"\""
val notQuote = predicate (fn x => x <> quote)
val string = literal quote *> many notQuote <* literal quote

fun head nil = nil
  | head (x::_) = x
fun parse f = f o String.explode
