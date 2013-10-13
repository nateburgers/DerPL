(* Evaluator for a Language (c) Nathan Burgers 2013 *)

infix 4 @>
datatype ('a, 'b) assoc = @> of 'a * 'b
type 'b dict = (string, 'b) assoc list

infix 2 o
fun opo (f,g)= fn x => f (g x)

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

fun oneOf (x::nil) = literal x
  | oneOf (x::xs) = literal x || oneOf xs
val charIn = oneOf o String.explode

val symbol = charIn "~`!@#$%^&*()-_=+[{]}\\|;:'\",<.>/?"



fun parse f = f o String.explode

		      (* Semantics *)
infixr 4 <| |>
datatype 'a stack = Bot
		  | |> of 'a * ('a stack)

type 'a combinator = 'a stack -> 'a stack
	       
datatype value = Number of real
	       | String of string
	       | Bool of bool
	       | Quote of value combinator stack
	       | Nil

fun lift1 f (a|>bs) = (f a) |> bs
fun lift2 f (a|>b|>cs) = (f a b) |> cs
fun lift3 f (a|>b|>c|>ds) = (f a b c) |> ds

fun lookup index ((key @> value)::nil) =
    if index = key then value else raise Match
  | lookup index ((key @> value)::dict) =
    if index = key then value else lookup index dict

fun dup Bot = Bot
  | dup (x |> s) = x |> x |> s
fun drop Bot = Bot
  | drop (x |> s) = s

fun liftArith f (Number x) (Number y) = Number (f x y)
  | liftArith f _ _ = Nil
val liftOp = lift2 o liftArith o curry

val prelude : value combinator dict
    = [ "*" @> liftOp op*
      , "/" @> liftOp op/
      , "+" @> liftOp op+
      , "-" @> liftOp op-
      , "dup" @> dup
      , "drop" @> drop
      ]

type ('a, 'b) eval = 'b * ('a dict)
fun compose f g x = f (g x)
fun fold f (x::y::nil) = f x y
  | fold f (x::xs) = f x (fold f xs)
fun bind fs x = (fold compose fs) x

fun eval fs x = bind (map (fn x => lookup x prelude) fs) x

val test = eval ["*", "dup"] (Number 2.0 |> Bot)

