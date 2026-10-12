#show figure.where(kind: raw): set figure(kind: "figure")
#show figure: set figure(supplement: [Figure])
#import "@preview/curryst:0.6.0": prooftree, rule

#let tensor = math.times.o
#let oplus = math.plus.o

#align(center)[
  #text(18pt, weight: "bold")[Linear Haskell]\
  #text(13pt)[Practical Linearity in a Higher-Order Polymorphic Language]\
  #v(1em)
  #smallcaps[Jean-Philippe Bernardy], University of Gothenburg, Sweden\
  #smallcaps[Mathieu Boespflug], Tweag I/O, France\
  #smallcaps[Ryan R. Newton], Indiana University, USA\
  #smallcaps[Simon Peyton Jones], Microsoft Research, UK\
  #smallcaps[Arnaud Spiwack], Tweag I/O, France
]

#v(1em)
#quote(block: true)[
  #strong[Abstract]

  Linear type systems have a long and storied history, but not a clear path forward to integrate with existing languages such as OCaml or Haskell. In this paper, we study a linear type system designed with two crucial properties in mind: backwards-compatibility and code reuse across linear and non-linear users of a library. Only then can the benefits of linear types permeate conventional functional programming. Rather than bifurcate types into linear and non-linear counterparts, we instead attach linearity to function arrows. Linear functions can receive inputs from linearly-bound values, but can also operate over unrestricted, regular values.
  To demonstrate the efficacy of our linear type system — both how easy it can be integrated in an existing language implementation and how streamlined it makes it to write programs with linear types — we implemented our type system in #smallcaps[ghc], the leading Haskell compiler, and demonstrate two kinds of applications of linear types: mutable data with pure interfaces; and enforcing protocols in I/O-performing functions.
]

= Introduction
<sec:introduction>
Despite their obvious promise, and a huge research literature, linear
type systems have not made it into mainstream programming languages,
even though linearity has inspired uniqueness typing in Clean, and
ownership typing in Rust. We take up this challenge by extending Haskell
with linear types. Our design supports many applications for linear
types, but we focus on two particular use-cases. First, safe
update-in-place for mutable structures, such as arrays; and second,
enforcing access protocols for external #smallcaps[api];s, such as
files, sockets, channels and other resources. Our particular
contributions are these:

- We describe an extension to Haskell for linear types, dubbed Linear
  Haskell, using two extended examples (Sec. 2.1--Sec. 2.3). The extension is
  #emph[non-invasive];: existing programs continue to typecheck, and
  existing datatypes can be used as-is even in linear parts of the
  program. The key to this non-invasiveness is that, in contrast to most
  other approaches, we focus on #emph[linearity on the function arrow]
  rather than #emph[linearity in the kinds] (Sec. 6.1).

- Every function arrow can be declared linear, including those of
  constructor types. This results in datatypes which can store both
  linear values, in addition to unrestricted ones
  (Sec. 2.4--2.5).

- A benefit of linearity-on-the-arrow is that it naturally supports
  #emph[linearity polymorphism] (Sec. 2.6). This contributes to a smooth
  extension of Haskell by allowing many existing functions (map,
  compose, etc) to be given more general types, so they can work
  uniformly in both linear and non-linear code.

- We formalise our system in a small, statically-typed core calculus
  that exhibits all these features (Sec. 3). It enjoys the usual properties of
  progress and preservation.

- We have implemented a prototype of the system as a modest extension to
  #smallcaps[ghc] (Sec. 4), which substantiates our claim of non-invasiveness.
  We use this prototype to implement case-study applications (Sec. 5). Our
  prototype performs linearity #emph[inference];, but a systematic
  treatment of type inference for linearity in our system remains open.

Retrofits often involve compromise and ad-hoc choices, but in fact we
have found that, as well as fitting into Haskell, our design holds
together in its own right. We hope that it may perhaps serve as a
template for similar work in other languages. There is a rich literature
on linear type systems, as we discuss in a long related work section (Sec. 6).

= Motivation and intuitions
<sec:programming-intro>
Informally, #emph[a function is "linear" if it consumes its argument
  exactly once];. (It is "affine" if it consumes it at most once.) A
linear type system gives a static guarantee that a claimed linear
function really is linear. There are many motivations for linear type
systems, but here we focus on two of them:

- #emph[Is it safe to update this value in-place] (Sec. 2.2)? That depends on
  whether there are aliases to the value; update-in-place is
  #smallcaps[ok] if there are no other pointers to it. Linearity
  supports a more efficient implementation, by $O \( 1 \)$ update rather
  than $O \( n \)$ copying.

- #emph[Am I obeying the usage protocol of this external resource] (Sec. 2.3)?
  For example, an open file should be closed, and should not be used
  after it it has been closed; a socket should be opened, then bound,
  and only then used for reading; a malloc'd memory block should be
  freed, and should not be used after that. Here, linearity does not
  affect efficiency, but rather eliminates many bugs.

We introduce our extension to Haskell, which we call Linear Haskell, by
focusing on these two use-cases. In doing so, we introduce a number of
ideas that we flesh out in subsequent subsections.

== Operational intuitions
<sec:consumed>
We have said informally that #emph["a linear function consumes its
  argument exactly once"];. But what exactly does that mean?

#quote(block: true)[
  #emph[Meaning of the linear arrow];:
  $sans(f) : : sans(s) multimap sans(t)$ guarantees that if
  $\( sans(f) sans(u) \)$ is consumed exactly once, then the
  argument $sans(u)$ is consumed exactly once.
]

To make sense of this statement we need to know what "consumed exactly
once" means. Our definition is based on the type of the value concerned:

#block[
  - To consume a value of atomic base type (like $sans("Int")$ or
  $sans("Ptr")$) exactly once, just evaluate it.

  - To consume a function value exactly once, apply it to one argument,
    and consume its result exactly once.

  - To consume a pair exactly once, pattern-match on it, and consume each
    component exactly once.

  - In general, to consume a value of an algebraic datatype exactly once,
    pattern-match on it, and consume all its linear components exactly
    once (Sec. 2.5)#footnote[You may deduce that pairs have linear components, and
      indeed they do, as we discuss in Sec. 2.5.] <def:consume>;.

]
This definition is enough to allow programmers to reason about the
typing of their functions, and it drives the formal typing judgements in
Sec. 3.

Note that a linear arrow specifies #emph[how the function uses its
  argument];. It does not restrict #emph[the arguments to which the
  function can be applied];. In particular, a linear function cannot
assume that it is given the unique pointer to its argument. For example,
if $sans(f) : : sans(s) multimap sans(t)$, then~this is fine:
```haskell
g :: s -> t
g x = f x
```
The type of $sans(g)$ makes no particular guarantees about the way in
which it uses $sans(x)$; in particular, $sans(g)$ can pass that argument
to $sans(f)$.

== Safe mutable arrays
<sec:freezing-arrays>
The Haskell language provides immutable arrays, built with the function
$sans("array")$#footnote[Haskell actually generalises over the type of
  array indices, but for this paper we will assume that the arrays are
  indexed, from 0, by $sans("Int")$ indices.];:
```haskell
array :: Int -> [(Int, a)] -> Array a
```

#figure(
  ```haskell
  type MArray s a
  type Array a
  newMArray :: Int -> ST s (MArray s a)
  read :: MArray s a -> Int -> ST s a
  write :: MArray s a -> (Int, a) -> ST s ()
  unsafeFreeze :: MArray s a -> ST s (Array a)
  forM_ :: Monad m =>
    [a] -> (a -> m ()) -> m ()
  runST :: (forall s. ST s a) -> a
  ```,
  caption: [
    Signatures for array primitives (current #smallcaps[ghc])
  ],
) <fig:array-sigs>

But how is $sans("array")$ implemented? A possible answer is "it is
built-in; don't ask". But in reality #smallcaps[ghc] implements
$sans("array")$ using more primitive pieces, so that library authors can
readily implement more complex variations --- and they certainly do: see
for example Sec. 5.1. Here is the definition of $sans("array")$, using library
functions whose types are given in Fig. 1.

```haskell
array :: Int -> [(Int, a)] -> Array a
array size pairs = runST
  (do { ma <- newMArray size
      ; forM_ pairs (write ma)
      ; unsafeFreeze ma })
```
In the first line we allocate a mutable array, of type
$sans("MArray") sans(s) sans(a)$. Then we iterate over the
$sans("pairs")$, with $sans("forM_")$, updating the array in place for
each pair. Finally, we freeze the mutable array, returning an immutable
array as required. All this is done in the $sans("ST")$ monad, using
$sans("runST")$ to securely encapsulate an imperative algorithm in a
purely-functional context, as described in @launchbury_st_1995.

Why is $sans("unsafeFreeze")$ unsafe? The result of
$\( sans("unsafeFreeze") sans("ma") \)$ is a new immutable array,
but to avoid an unnecessary copy, it is actually $sans("ma")$. The
intention is, of course, that that $sans("unsafeFreeze")$ should be the
last use of the mutable array; but nothing stops us continuing to mutate
it further, with quite undefined semantics. The 'unsafe'' in the
function name is a #smallcaps[ghc] convention meaning 'the programmer
has a proof obligation here that the compiler cannot check''.

The other unsatisfactory thing about the monadic approach to array
construction is that it is overly sequential. Suppose you had a pair of
mutable arrays, with some updates to perform to each; these updates
could be done in #emph[parallel];, but the $sans("ST")$ monad would
serialise them.

Linear types allow a more secure and less sequential interface. Linear
Haskell introduces a new kind of function type: the #emph[linear arrow]
$sans(a) multimap sans(b)$. A linear function
$sans(f) : : sans(a) multimap sans(b)$ must consume its argument
#emph[exactly once];. This new arrow is used in a new array
#smallcaps[api];, given in Fig. 2.

#figure(
  ```haskell
  type MArray a
  type Array a
  newMArray :: Int -> (MArray a ⊸ Unrestricted b) ⊸ b
  write :: MArray a ⊸ (Int, a) -> MArray a
  read :: MArray a ⊸ Int -> (MArray a, Unrestricted a)
  freeze :: MArray a ⊸ Unrestricted (Array a)
  ```,
  caption: [
    Type signatures for array primitives (linear version), allowing
    in-place update.
  ],
)
<fig:linear-array-sigs>

Using this #smallcaps[api] we can define $sans("array")$ thus:
```haskell
array :: Int -> [(Int, a)] -> Array a
array size pairs = newMArray size (λma -> freeze (foldl write ma pairs))
```
There are several things to note here:

- The function $sans("newMArray")$ allocates a fresh, mutable array of the
  specified size, and passes it to the function supplied as the second
  argument to $sans("newMArray")$, as a #emph[linear] value $sans("ma")$.

- Even though linearity is a property of function arrows, not of types
  (Sec. 6.1), we still disinguish the type of mutable arrays $sans("MArray")$ from
  that of immutable arrays $sans("Array")$, because in this api only
  immutable arrays are #emph[allowed] to be non-linear (unrestricted).
  The way to say that results can be freely shared is to use
  $sans("Unrestricted")$ (our version of linear logic's $!$ modality, see
  Sec. 2.4), as in the type of $sans("freeze")$.

- Because $sans("freeze")$ consumes its input, there is no danger of the
  same mutable array being subsequently written to, eliminating the
  problem with $sans("unsafeFreeze")$.

- Since $sans("ma")$ is linear, we can only use it once. Thus each call to
  $sans("write")$ returns a (logically) new array, so that the array is
  single-threaded, by $sans("foldl")$, through the sequence of writes.

- Above, $sans("foldl")$ has the type
  $\( sans(a) multimap sans(b) multimap sans(a) \) arrow.r sans(a) multimap \[ sans(b) \] multimap sans(a)$,
  which expresses that it consumes its second argument linearly (the
  mutable array), while the function it is given as its first argument
  ($sans("write")$) must be linear. As we shall see in Sec. 2.6 this is not a new
  $sans("foldl")$, but an instance of a more general,
  multiplicity-polymorphic version of a single $sans("foldl")$ (where
  "multiplicity" refers to how many times a function consumes its
  input).

Three factors ensure that a unique $sans("MArray")$ is needed in any given
application $sans(x) = sans("newMArray") sans(k)$, and in turn
that update-in-place is safe. First, $sans("newMArray")$ introduces
#emph[only] a linear $sans("ma") : : sans("MArray") sans(a)$.
Second, no function that consumes an $sans("MArray") sans(a)$
returns more than a #emph[single] pointer to it; so $sans(k)$ can never
obtain two pointers to $sans("ma")$. Third, $sans(k)$ must wrap its result
in $sans("Unrestricted")$. This third point means that even if $sans(x)$
is used in an unrestricted way, it suffices to call $sans(k)$ a single
time to obtain the result, and in turn no mutable pointer to $sans("ma")$
can #emph[escape] when $sans("newArray")$ returns (#emph[i.e.] when the
$sans(b)$ result of $sans("newArray")$ is evaluated).

With this mutable array #smallcaps[api];, the $sans("ST")$ monad has
disappeared altogether; it is the array #emph[itself] that must be
single threaded, not the operations of a monad. That removes the
unnecessary sequentialisation we mentioned earlier and opens the
possibility of exploiting more parallelism at runtime.

Compared to the #emph[status quo] (using $sans("ST")$ and
$sans("unsafeFreeze")$), the other major benefit is in shrinking the
trusted code base, because more library code (and it can be particularly
gnarly code) is statically typechecked. Clients who use only
#emph[immutable] arrays do not see the inner workings of the library,
and will be unaffected. Of course, the functions of Fig. 2 are still part of
the trusted code base, in particular, they must not lie about linearity.
Our second use-case has a much more direct impact on library clients.

== I/O protocols
<sec:io-protocols>
#grid(
  columns: (1fr, 1fr),
  gutter: 1.5em,
  [
    #figure(
      ```haskell
      type File
      openFile :: FilePath -> IO File
      readLine :: File -> IO ByteString
      closeFile :: File -> IO ()
      ```,
      caption: [Types for traditional file IO],
    ) <fig:io-trad>
  ],
  [
    #figure(
      ```haskell
      type File
      openFile :: FilePath -> IOL 1 File
      readLine :: File ⊸ IOL 1 (File, Unrestricted ByteString)
      closeFile :: File ⊸ IOL ω ()
      ```,
      caption: [Types for linear file IO],
    ) <fig:io-linear>
  ],
)

Consider the #smallcaps[api] for files in Fig. 3, where a $sans("File")$ is a
cursor in a physical file. Each call to $sans("readLine")$ returns a
$sans("ByteString")$ (the line) and moves the cursor one line forward. But
nothing stops us reading a file after we have closed it, or forgetting
to close it. An alternative #smallcaps[api] using linear types is given
in Fig. 4. Using it we can write a simple file handling program,
$sans("firstLine")$, shown here.
```haskell
firstLine :: FilePath -> IOL ω Bytestring
firstLine fp =
  do { f <- openFile fp
     ; (f, Unrestricted bs) <- readLine f
     ; closeFile f
     ; return bs }
```
Notice several things:

- Operations on files remain monadic, unlike the case with mutable
  arrays. I/O operations affect the world, and hence must be sequenced.
  It is not enough to sequence operations on files individually, as it
  was for arrays.

- We generalise the $sans("IO")$ monad so that it expresses whether or not
  the returned value is linear. We add an extra #emph[multiplicity] type
  parameter $sans(p)$ to the monad $sans("IO")_(sans(L))$, where $sans(p)$
  can be $upright(1)$ or $omega$, indicating a linear or unrestricted
  result, respectively. Now $sans("openFile")$ returns
  $sans("IO")_(sans(L)) upright(1) sans("File")$, the
  "$upright(1)$" indicating that the returned $sans("File")$ must be used
  linearly. We will return to how $sans("IO")_(sans(L))$ is defined in Sec. 2.7.

- As before, operations on linear values must consume their input and
  return a new one; here $sans("readLine")$ consumes the $sans("File")$ and
  produces a new one.

- Unlike the $sans("File")$, the $sans("ByteString")$ returned by
  $sans("readLine")$ is unrestricted, and the type of $sans("readLine")$
  indicates this.

It may seem tiresome to have to thread the $sans("File")$ as well as
sequence operations with the $sans("IO")$ monad. But in fact it is often
useful do to do so, because we can use types to witness the state of the
resource, #emph[e.g.];, with separate types for an open or closed
$sans("File")$. We show applications in Sec. 5.1 and Sec. 5.2.

== Linear datatypes
<sec:linear-constructors>

With the above intutions in mind, what type should we assign to a data
constructor such as the pairing constructor $\( \, \)$? Here are two
possibilities:

```haskell
(, ) :: a ⊸ b ⊸ (a, b)       (, ) :: a -> b -> (a, b)
```
Using the definition in Sec. 2.1, the former is clearly the correct choice: if
the result of $\( \, \) sans("e1") sans("e2")$ is consumed
exactly once, then (by Def. 2.1), $sans("e1")$ and $sans("e2")$ are each consumed
exactly once; and hence $\( \, \)$ is linear it its arguments.

```haskell
f1 :: (Int, Int) -> (Int, Int)
f1 x = case x of (a, b) -> (a, a)

f2 :: (Int, Int) ⊸ (Int, Int)
f2 x = case x of (a, b) -> (b, a)
```
So much for construction; what about pattern matching? Consider
$sans("f1")$ and $sans("f2")$ defined here; $sans("f1")$ is an ordinary
Haskell function. Even though the data constructor $\( \, \)$ has a
linear type, that does #emph[not] imply that the pattern-bound variables
$sans(a)$ and $sans(b)$ must be consumed exactly once; and indeed they
are not. Therefore, $sans("f1")$ does not have the linear type
$\( sans("Int") \, sans("Int") \) multimap \( sans("Int") \, sans("Int") \)$.
Why not? If the result of $\( sans("f1") sans(t) \)$ is consumed
once, is $sans(t)$ guaranteed to be consumed once? No: $sans(t)$ is
guaranteed to be evaluated once, but its first component is then
consumed twice and its second component not at all, contradicting Def. 2.1. In
contrast, $sans("f2")$ #emph[does] have a linear type: if
$\( sans("f2") sans(t) \)$ is consumed exactly once, then indeed
$sans(t)$ is consumed exactly once. The key point here is that #emph[the
  same pair constructor works in both functions; we do not need a special
  non-linear pair];.

The same idea applies to all existing Haskell datatypes: in Linear
Haskell we treat all datatypes defined using legacy Haskell-98
(non-#smallcaps[gadt];) syntax as defining constructors with linear
arrows. For example here is a declaration of Linear Haskell's list type,
whose constructor $\( : \)$ uses linear arrows:

```haskell
data [a] = [ ] | a : [a]

(++) :: [a] ⊸ [a] ⊸ [a]
[ ] ++ ys = ys
(x : xs) ++ ys = x : (xs ++ ys)
```
Just as with pairs, this is not a new, linear list type: this #emph[is]
Linear Haskell's list type, and all existing Haskell functions will work
over it perfectly well. Even better, many list-based functions are in
fact linear, and can be given a more precise type. For example we can
write (++) as follows:

This type says that if
$\( sans("xs") ++ sans("ys") \)$ is consumed
exactly once, then $sans("xs")$ is consumed exactly once, and so is
$sans("ys")$, and indeed our type system will accept this definition.

As before, giving a more precise type to
(++) only #emph[strengthens] the
contract that (++) offers to its
callers; #emph[it does not restrict its usage];. For example:
```haskell
sum :: [Int] ⊸ Int
f :: [Int] ⊸ [Int] -> Int
f xs ys = sum (xs ++ ys) + sum ys
```
Here the two arguments to (++) have
different multiplicities, but the function $sans(f)$ guarantees that it
will consume $sans("xs")$ exactly once if
$\( sans(f) sans("xs") sans("ys") \)$ is consumed exactly
once.

For an existing language, being able to strengthen
(++), and similar functions, in a
#emph[backwards-compatible] way is a huge boon. Of course, not all
functions are linear: a function may legitimately demand unrestricted
input. For example, the function $sans(f)$ above consumes $sans("ys")$
twice, and so $sans(f)$ needs an unrestricted arrow for that argument.
<sec:compatibility>

Finally, we can use the very same pairs and lists types to contain
linear values (such as mutable arrays) without compromising safety. For
example:
```haskell
upd :: (MArray Char, MArray Char) ⊸ Int -> (MArray Char, MArray Char)
upd (a1, a2) n | n >= 10   = (write a1 n 'x', a2)
               | otherwise = (write a2 n 'o', a1)
```

== Unrestricted data constructors
<sec:non-linear-constructors>
Suppose we want to pass a linear $sans("MArray")$ and an unrestricted
$sans("Int")$ to a function $sans(f)$. We could give $sans(f)$ the
signature
$sans(f) : : sans("MArray") sans("Int") multimap sans("Int") arrow.r sans("MArray") sans("Int")$.
But suppose we wanted to uncurry the function; we could then give it the
type:
```haskell
f :: (MArray Int, Int) ⊸ MArray Int
```
But this is no good: now $sans(f)$ is only allowed to use the
$sans("Int")$ linearly, but it might actually use it many times. For this
reason it is extremely useful to be able to declare data constructors
with non-linear types, like this:
```haskell
data PLU a b where { PLU :: a ⊸ b -> PLU a b }
f :: PLU (MArray Int) Int ⊸ MArray Int
```
Here we use #smallcaps[gadt];-style syntax to give an explicit type
signature to the data constructor $sans("PLU")$, with mixed linearity.
Now, when #emph[constructing] a $sans("PLU")$ pair the type of the
constructor means that we must always supply an unrestricted second
argument; and dually when #emph[pattern-matching] on $sans("PLU")$ we are
therefore free to use the second argument in an unrestricted way, even
if the $sans("PLU")$ value itself is linear.

Instead of defining a pair with mixed linearity, we can also write:
```haskell
data Unrestricted a where { Unrestricted :: a -> Unrestricted a }
f :: (MArray Int, Unrestricted Int) ⊸ MArray Int
```
The type $\( sans("Unrestricted") sans(t) \)$ is very much
like "$! sans(t)$" in linear logic, but in our setting it is just an
ordinary user-defined datatype. We saw it used in Fig. 2, where the result of
$sans("read")$ was a pair of a linear $sans("MArray")$ and an unrestricted
array element:
```haskell
read :: MArray a ⊸ Int -> (MArray a, Unrestricted a)
```
Note that, according to the definition in Sec. 2.1, if a
value of type $\( sans("Unrestricted") sans(t) \)$ is consumed
exactly once, that tells us nothing about how the argument of the data
constructor is consumed: it may be consumed many times or not at all.

== Multiplicity polymorphism
<sec:lin-poly>
A linear function provides more guarantees to its caller than a
non-linear one~---~it is more general. But the higher-order case
thickens the plot. Consider the standard $sans("map")$ function over
(linear) lists:
```haskell
map f [ ] = [ ]
map f (x : xs) = f x : map f xs
```
It can be given the two following incomparable types:
$\( sans(a) multimap sans(b) \) arrow.r \[ sans(a) \] multimap \[ sans(b) \]$
and
$\( sans(a) arrow.r sans(b) \) arrow.r \[ sans(a) \] arrow.r \[ sans(b) \]$.
Thus, Linear Haskell features quantification over multiplicities and
parameterised arrows ($sans(A) arrow.r_(sans(q)) sans(B)$).
Using these, $sans("map")$ can be given the following more general type:
$forall sans(p) . \( sans(a) arrow.r_(sans(p)) sans(b) \) arrow.r \[ sans(a) \] arrow.r_(sans(p)) \[ sans(b) \]$.
Likewise, function composition and $sans("foldl")$ (#emph[cf.] Section 2.2) can be
given the following general types:
```haskell
foldl :: ∀p q. (a ->p b ->q a) -> a ->p [b] ->q a
(◦) :: ∀p q. (b ->p c) ⊸ (a ->q b) ->p a ->p·q c
(f ◦ g) x = f (g x)
```
The type of $\( compose \)$ says that two functions that accept
arguments of arbitrary multiplicities ($sans(p)$ and $sans(q)$
respectively) can be composed to form a function accepting arguments of
multiplicity $sans(p) dot.c sans(q)$ (#emph[i.e.] the product of
$sans(p)$ and $sans(q)$ --- see Def. 3.4). Finally, from a
backwards-compatibility perspective, all of these subscripts and binders
for multiplicity polymorphism can be ignored. Indeed, in a context where
client code does not use linearity, all inputs will have unlimited
multiplicity, $omega$, and transitively all expressions can be promoted
to $omega$. Thus in such a context the compiler, or indeed documentation
tools, can even altogether hide linearity annotations from the
programmer when this language extension is not turned on.

== Linear input/output
<sec:linear-io>
In Sec. 2.3 we introduced the $sans("IO")_(sans(L))$
monad.#footnote[$sans("IO")_(sans(L)) sans(p)$ is not a monad in
  the strict sense, because $sans(p)$ and $sans(q)$ can be different in
  $sans("bind")_(sans("IO")_(sans(L)))$. However it is a relative
  monad~@altenkirch_monads_2010. The details, involving the functor
  $bold("data") sans("Mult") sans(p) sans(a) bold("where") { sans("Mult") : : sans(a) arrow.r_(sans(p)) sans("Mult") sans(p) sans(a) }$
  and linear arrows, are left as an exercise to the reader.] But how does
it work? $sans("IO")_(sans(L))$ is just a generalisation of the $sans("IO")$
monad, thus:
```haskell
type IOL p a
returnIOL :: a ->p IOL p a
bindIOL :: IOL p a ⊸ (a ->p IOL q b) ⊸ IOL q b
```
The idea is that if
$sans(m) : : sans("IO")_(sans(L)) upright(1) sans(t)$,
then $sans(m)$ is an input/output computation that returns a linear
value of type $sans(t)$. But what does it mean to "return a linear
value" in a world where linearity applies only to function arrows?
Fortunately, in the world of monads each computation has an explicit
continuation, so we just need to control the linearity of the
continuation arrow. More precisely, in an application
$sans(m) med sans("bind")_(sans("IO")_(sans(L))) med sans(k)$
where
$sans(m) : : sans("IO")_(sans(L)) upright(1) sans(t)$, we
need the continuation $sans(k)$ to be linear,
$sans(k) : : sans(t) multimap sans("IO")_(sans(L)) sans(q) sans("t'")$.
And that is captured by the multiplicity-polymorphic type of
$sans("bind")_(sans("IO")_(sans(L)))$.

Even though they have a different type than usual, the bind and return
combinators of $sans("IO")_(sans(L))$ can be used in the familiar way. The
difference with the usual monad is that multiplicities may be mixed, but
this poses no problem in practice. Consider:
```haskell
printHandle :: File ⊸ IO ω ()
printHandle f = do
  { (f, Unrestricted b) <- atEOF f -- atEOF :: File ⊸ IOL 1 (File, Unrestricted Bool)
  ; if b then closeFile f         -- closeFile :: File ⊸ IOL ω ()
    else do { (f, Unrestricted c) <- read f -- read :: File ⊸ IOL 1 (File, Unrestricted Char)
            ; putChar c                    -- putChar :: Char -> IOL ω ()
            ; printHandle f } }
```
Here $sans("atEOF")$ and $sans("read")$ return a linear $sans("File")$
that should be closed, but $sans("close")$ and $sans("putChar")$ return an
ordinary non-linear $\( \)$. So this sequence of operations has mixed
linearity. Nevertheless, we can interpret the
$bold("do")$-notation with $sans("bind")_(sans("IO")_(sans(L)))$ in
the usual way:
```haskell
read f `bindIOL` λ(f, Unrestricted c) ->
putChar c `bindIOL` λ_ -> ...
```
Such an interpretation of the
$bold("do")$-notation requires Haskell's `-XRebindableSyntax`
extension, but if linear I/O becomes commonplace it would be worth
considering a more robust solution.

Internally, hidden from clients, #smallcaps[ghc] actually implements
$sans("IO")$ as a function, and that implementation too is illuminated by
linearity, like so:
```haskell
data World
newtype IOL p a = IOL {unIOL :: World ⊸ IORes p a}
data IORes p a where
  IOR :: World ⊸ a ->p IORes p a

bindIOL :: IOL p a ⊸ (a ->p IOL q b) ⊸ IOL q b
bindIOL (IOL m) k = IOL (λw -> case m w of
  IOR w' r -> unIOL (k r) w')
```
A value of type $sans("World")$ represents the
state of the world, and is threaded linearly through I/O computations.
The linearity of the result of the computation is captured by the
$sans(p)$ parameter of $sans("IO")_(sans(L))$, which is inherited by the
specialised form of pair, $sans("IORes")$ that an $sans("IO")_(sans(L))$
computation returns. All linearity checks are verified by the compiler,
further reducing the size of the trusted code base.

== Linearity and strictness
<linearity-and-strictness>
It is tempting to assume that, since a linear function consumes its
argument exactly once, then it must also be strict. But not so! For
example:
```haskell
f :: a ⊸ (a, Bool)
f x = (x, True)
```
Here $sans(f)$ is certainly linear according to Sec. 2.1, and given the type
of $\( \, \)$ in Sec. 2.4. That is, if $\( sans(f) sans(x) \)$ is
consumed exactly once, then each component of its result pair is
consumed exactly once, and hence $sans(x)$ is consumed exactly once. But
$sans(f)$ is certainly not strict: $sans(f) tack.t$ is not
$tack.t$.

= $lambda_arrow.r^q$: a core calculus for Linear Haskell
<sec:statics>

We do not formalise all of Linear Haskell, but rather a core calculus,
$lambda_arrow.r^q$ which exhibits all key features, including datatypes
and multiplicity polymorphism. This way we make precise much of the
informal discussion above.

== Syntax
<sec:syntax>

#figure(
  align(center)[
    #grid(
      columns: (1fr, 1fr),
      gutter: 1.5em,
      align: left,
      [
        #strong[Multiplicities]\
        $ pi, mu ::= 1 | omega | p | pi + mu | pi dot.c mu $
      ],
      [
        #strong[Types]\
        $ A, B ::= A arrow.r_pi B | forall p. A | D med p_1 dots.h p_n $
      ],
    )
    #v(0.5em)
    #grid(
      columns: (1fr, 1.2fr),
      gutter: 1.5em,
      align: left,
      [
        #strong[Contexts]\
        $ Gamma, Delta ::= (x :_mu A), Gamma | tack.r $
      ],
      [
        #strong[Datatype declaration]\
        $
          sans("data") D med p_1 dots.h p_n med sans("where") (c_k : A_1 arrow.r_(pi_1) dots.h A_(n_k) arrow.r_(pi_(n_k)) D)_(k=1)^m
        $
      ],
    )
    #v(0.5em)
    #align(left)[
      #strong[Terms]\
      $
        e, s, t, u ::= & x & upright("variable") \
        | & lambda_pi (x:A).t & upright("abstraction") \
        | & t med s & upright("application") \
        | & lambda p.t & upright("multiplicity abstraction") \
        | & t med pi & upright("multiplicity application") \
        | & c med t_1 dots.h t_n & upright("data construction") \
        | & sans("case")_pi t sans("of") { c_k x_1 dots.h x_(n_k) arrow.r u_k }_(k=1)^m & upright("case") \
        | & sans("let")_pi x_1 : A_1 = t_1 dots.h x_n : A_n = t_n sans("in") u & upright("let")
      $
    ]
  ],
  caption: [
    Syntax of $lambda_arrow.r^q$
  ],
) <fig:contexts>

The term syntax of $lambda_arrow.r^q$ is that of a type-annotated
(#emph[à la] Church) simply-typed $lambda$-calculus with let-definitions
(Fig. 5). It includes multiplicity polymorphism, but to avoid clutter we omit
ordinary type polymorphism.

$lambda_arrow.r^q$ is an explicitly-typed language: each binder is
annotated with its type and multiplicity; and multiplicity abstraction
and application are explicit. Linear Haskell will use type inference to
fill in much of this information, but we do not address the challenges
of type inference here.

The types of $lambda_arrow.r^q$ (see Fig. 5) are simple types with arrows
(albeit multiplicity-annotated ones), datatypes, and multiplicity
polymorphism. We use the following abbreviations:
$A arrow.r B eq.def A arrow.r_omega B$ and
$A multimap B eq.def A arrow.r_1 B$. Datatype declarations (see Fig. 5) are of
the following form:
$
  sans("data") D med p_1 med dots.h med p_n med sans("where") (c_k : A_1 arrow.r_(pi_1) dots.h.c A_(n_k) arrow.r_(pi_(n_k)) D)_(k = 1)^m
$
The above declaration means that $D$ is parameterized over $n$
multiplicities $p_i$ and has $m$ constructors $c_k$, each with $n_k$
arguments. Arguments of constructors have a multiplicity, just like
arguments of functions: an argument of multiplicity $omega$ means that
consuming the data constructor once makes no claim on how often that
argument is consumed (Def. 2.1). All the variables in the multiplicities $pi_i$
must be among $p_1 dots.h p_n$; we write $pi [pi_1 dots.h pi_n]$ for
the substitution of $p_i$ by $pi_i$ in $pi$.

== Static semantics
<sec:typing-contexts>

#figure(
  align(center)[
    #set text(size: 8.5pt)
    #grid(
      columns: (1fr, 1fr),
      gutter: 1.5em,
      prooftree(rule(
        name: "var",
        $omega Gamma + x :_1 A tack.r x : A$,
      )),
      prooftree(rule(
        name: "abs",
        $Gamma, x :_pi A tack.r t : B$,
        $Gamma tack.r lambda_pi (x:A).t : A arrow.r_q B$,
      )),
    )
    #v(0.6em)
    #prooftree(rule(
      name: "app",
      $Gamma tack.r t : A arrow.r_pi B$,
      $Delta tack.r u : A$,
      $Gamma + pi Delta tack.r t u : B$,
    ))
    #v(0.6em)
    #prooftree(rule(
      name: "con",
      $Delta_i tack.r t_i : A_i$,
      $c_k : A_1 arrow.r_(mu_1) dots.h arrow.r_(mu_(n_k - 1)) A_(n_k) arrow.r_(mu_(n_k)) D med p_1 dots.h p_n upright(" constructor")$,
      $omega Gamma + sum_i mu_i [pi_1 dots.h pi_n] Delta_i tack.r c_k t_1 dots.h t_(n_k) : D med pi_1 dots.h pi_n$,
    ))
    #v(0.6em)
    #prooftree(rule(
      name: "case",
      $Gamma tack.r t : D med pi_1 dots.h pi_n$,
      $Delta, x_1 :_(pi mu_1 [pi_1 dots.h pi_n]) A_1, dots.h, x_(n_k) :_(pi mu_(n_k) [pi_1 dots.h pi_n]) A_(n_k) tack.r u_k : C$,
      $upright("for each ") c_k : A_1 arrow.r_(mu_1) dots.h arrow.r_(mu_(n_k - 1)) A_(n_k) arrow.r_(mu_(n_k)) D med p_1 dots.h p_n$,
      $pi Gamma + Delta tack.r sans("case")_pi t sans("of") { c_k x_1 dots.h x_(n_k) arrow.r u_k }_(k = 1)^m : C$,
    ))
    #v(0.6em)
    #prooftree(rule(
      name: "let",
      $Gamma_i tack.r t_i : A_i$,
      $Delta, x_1 :_pi A_1 dots.h x_n :_pi A_n tack.r u : C$,
      $Delta + pi sum_i Gamma_i tack.r sans("let")_pi x_1 : A_1 = t_1 dots.h x_n : A_n = t_n sans("in") u : C$,
    ))
    #v(0.6em)
    #grid(
      columns: (1fr, 1fr),
      gutter: 1.5em,
      prooftree(rule(
        name: "m.abs",
        $Gamma tack.r t : A$,
        $p upright(" fresh for ") Gamma$,
        $Gamma tack.r lambda p . t : forall p . A$,
      )),
      prooftree(rule(
        name: "m.app",
        $Gamma tack.r t : forall p . A$,
        $Gamma tack.r t pi : A [pi / p]$,
      )),
    )
  ],
  caption: [
    Typing rules
  ],
) <fig:typing>

The static semantics of $lambda_arrow.r^q$ is given in Fig. 6. Each binding in
$Gamma$, of form $x :_pi A$, includes a multiplicity $pi$ (Fig. 5). The
familiar judgement $Gamma tack.r t : A$ should be read as follows

#quote(block: true)[
  $Gamma tack.r t : A$ asserts that consuming the term $t : A$ exactly
  once will consume each binding $\( x :_pi A \)$ in $Gamma$ with its
  multiplicity $pi$.
]

One may want to think of the #emph[types] in $Gamma$ as inputs of the
judgement, and the #emph[multiplicities] as outputs.

The rule (abs) for lambda abstraction adds $\( x :_pi A \)$ to the
environment $Gamma$ before checking the body $sans(t)$ of the
abstraction. Notice that in $lambda_arrow.r^q$, the lambda abstraction
$lambda_pi \( x : A \) . t$ is explicitly annotated with multiplicity
$pi$. Remember, this is an explicitly-typed intermediate language; in
Linear Haskell this multiplicity is inferred.

The dual application rule (app) is more interesting:
#align(center)[
  #prooftree(rule(
    name: "app",
    $Gamma tack.r t : A arrow.r_pi B$,
    $Delta tack.r u : A$,
    $Gamma + pi Delta tack.r t u : B$,
  ))
]
To consume $\( sans(t) sans(u) \)$ once, we consume $sans(t)$
once, yielding the multiplicities in $Gamma$, and $sans(u)$ once,
yielding the multiplicies in $Delta$. But if the multiplicity $pi$ on
$sans(u)$'s function arrow is $omega$, then the function consumes its
argument not once but $omega$ times, so all $sans(u)$'s free variables
must also be used with multiplicity $omega$. We express this by
#emph[scaling] the multiplicities in $Delta$ by $pi$. Finally we need to
add together all the multiplicities in $Gamma$ and $pi Delta$; hence the
context $Gamma + pi Delta$ in the conclusion of the rule.

In writing this rule we needed to "scale" a context by a multiplicity,
and "add" two contexts. We pause to define these operations.

#block[
  ~
  $
    \( x :_pi A \, Gamma \) + \( x :_mu A \, Delta \) & = x :_(pi + mu) A \, \( Gamma + Delta \) \
                      \( x :_pi A \, Gamma \) + Delta & = x :_pi A \, Gamma + Delta              & \( x in.not Delta \) \
                                        \( \) + Delta & = Delta
  $

]
Context addition is total: if a variable occurs in both operands the
first rule applies (with possible re-ordering of bindings in $Delta$),
if not the second or third rule applies.

#block[
  $ pi \( x :_mu A \, Gamma \) = x :_(pi mu) A \, pi Gamma $

]
#block[
  The following laws hold:
  $
          Gamma + Delta & = Delta + Gamma       & pi \( Gamma + Delta \) & = pi Gamma + pi Delta \
    \( pi + mu \) Gamma & = pi Gamma + mu Gamma \
      \( pi mu \) Gamma & = pi \( mu Gamma \)   &                1 Gamma & = Gamma
  $

]
These operations depend, in turn, on addition and multiplication of
multiplicities. The syntax of multiplicities is given in Fig. 5. We need the
concrete multiplicities $1$ and $omega$ and, to support polymorphism,
multiplicity variables (ranged over by the metasyntactic variables $p$
and $q$) as well as formal sums and products of multiplicities.
Multiplicity expressions are quotiented by the following equivalence
relation:

#block[The equivalence of multiplicities is the
  smallest transitive and reflexive relation, which obeys the following
  laws:

  - $+$ and $dot.c$ are associative and commutative

  - $1$ is the unit of $dot.c$

  - $dot.c$ distributes over $+$

  - $omega dot.c omega = omega$

  - $1 + 1 = 1 + omega = omega + omega = omega$
] <def:equiv-multiplicity>
Thus, multiplicities form a semi-ring (without a zero), which extends to
a module structure on typing contexts. We may want to have a stronger
notion of equivalence for multiplicities, as we discuss in Sec. 3.5.

Returning to the typing rules in Fig. 6, the rule (let) is like a combination
of (abs) and (app). Again, each let binding is explicitly
annotated with its multiplicity. The variable rule (var) uses a standard
idiom: #align(center)[
  #prooftree(rule(name: "var", $omega Gamma + x :_1 A tack.r x : A$))
] This rule
allows us to ignore variables with multiplicity $omega$ (usually called
weakening), so that, for example $x :_1 A \, y :_omega B tack.r x : A$
holds #footnote[Pushing weakening to the variable rule is classic in
  many $lambda$-calculi, and in the case of linear logic, dates back at
  least to Andreoli's work on focusing~@andreoli_logic_1992.];. Note that
the judgement $x :_omega A tack.r x : A$ is an instance of the variable
rule, because $\( x :_omega A \) + \( x :_1 A \) = x :_omega A$.

Finally, abstraction and application for multiplicity polymorphism are
handled straightforwardly by (m.abs) and (m.app).

== Data constructors and case expressions
<sec:typing-rules>
The handling of data constructors and case expressions is a distinctive
aspect of our design. For constructor applications, the rule (con),
everything is straightforward: we treat the data constructor in
precisely the same way as an application of a function with that data
constructor's type. This includes weakening via the $omega Gamma$
context in the conclusion. The (case) rule is more interesting:
#align(center)[
  #prooftree(rule(
    name: "case",
    $Gamma tack.r t : D med pi_1 dots.h pi_n$,
    $Delta, x_1 :_(pi mu_1 [pi_1 dots.h pi_n]) A_1, dots.h, x_(n_k) :_(pi mu_(n_k) [pi_1 dots.h pi_n]) A_(n_k) tack.r u_k : C$,
    $upright("for each ") c_k : A_1 arrow.r_(mu_1) dots.h arrow.r_(mu_(n_k - 1)) A_(n_k) arrow.r_(mu_(n_k)) D med p_1 dots.h p_n$,
    $pi Gamma + Delta tack.r sans("case")_pi t sans("of") { c_k x_1 dots.h x_(n_k) arrow.r u_k }_(k = 1)^m : C$,
  ))
]
First, notice that the $sans("case")$ keyword is annotated with a
multiplicity $pi$; this is analogous to the explicit multiplicity on a
$sans("let")$ binding. It says how often the scrutinee (or, for a
$sans("let")$, the right hand side) will be consumed. Just as for
$sans("let")$, we expect $pi$ to be inferred from an un-annotated
$sans("case")$ in Linear Haskell.

The scrutinee $t$ is consumed $pi$ times, which accounts for the
$pi Gamma$ in the conclusion. Now consider the bindings
$\( x_i :_(pi mu_i \[ pi_1 dots.h pi_n \]) A_i \)$ in the environment
for typechecking $u_k$. That binding will be linear only if #emph[both]
$pi$ #emph[and] $pi_i$ are linear; that is, only if we specify that the
scrutinee is consumed once, and the $i$'th field of the data constructor
$c_k$ specifies that is it consumed once if the constructor is (Def. 2.1). To
put it another way, suppose one of the linear fields#footnote[Recall Sec. 2.5,
  which described how each constructor can have a mixture of linear and
  non-linear fields.] of $c_k$ is used non-linearly in $u_k$. Then,
$mu_i = 1$ (it is a linear field), so $pi$ must be $omega$, so that
$pi mu_i = omega$. In short, using a linear field non-linearly forces
the scrutinee to be used non-linearly, which is just what we want. Here
are some concrete examples:

```haskell
fst :: (a, b) -> a          swap :: (a, b) ⊸ (b, a)
fst (a, b) = a             swap (a, b) = (b, a)
```
Recall that both fields of a pair are linear (Sec. 2.4). In $sans("fst")$, the
second component of the pair is used non-linearly (by being discarded)
which forces the use of $sans("case")_omega$, and hence a non-linear
type for $sans("fst")$. But $sans("swap")$ uses the components linearly, so
we can use $sans("case")_1$, giving $sans("swap")$ a linear type.

== Metatheory
<sec:metatheory>
In order to prove that our type system meets its stated goals, we
introduce an operational semantics. The details are deferred to Appendix A.

==== Of consuming exactly once
<of-consuming-exactly-once>
The operational semantics is a big-step operational semantics for lazy
evaluation in the style of
#cite(<launchbury_natural_1993>, form: "prose");. Following
#cite(<gunter_partial-big-step_1993>, form: "prose");, starting from a
big-step evaluation relation $a arrow.b.double b$, we define
#emph[partial derivations] and from there a #emph[partial evaluation]
relation $a arrow.b.double^(\*) b$ (see Sec. A.1). Progress is expressed as the fact that a derivation of
$a arrow.b.double^(\*) b$ can always be extended.

The operational semantics differs from
#cite(<launchbury_natural_1993>, form: "prose");'s in two major
respects:

- The reduction states are heavily annotated with type information.
  These type annotations are used for the proofs.

- Reduction is indexed by whether we intend to consume the term under
  consideration exactly once or an arbitrary number of times

- Variables in the environments are annotated by a multiplicity ($1$ or
  $omega$), $omega$-variables are ordinary variables. When forced, an
  $omega$-variable is replaced by its value (to model lazy sharing), but
  $1$-variables #emph[must be consumed exactly once];: when forced, they
  are removed from the environment. Reduction gets stuck if a 1-variable
  is used more than once.

Because the operational semantics gets stuck if a 1-variable is used
more than once, the progress theorem (Theorem 3.6) shows that linear functions do
indeed consume their argument at most once if their result is consumed
exactly once. The 1-variables are in fact used exactly once: it is a
consequence of type preservation that evaluation of a closed term of a
basic type (say $sans("Bool")$) returns an environment with no
1-variables.

Our preservation and progress theorems (proved in Sec. A.3) read as follows:

#block[If $a$ is well typed, and $a arrow.b.double b$, or
  $a arrow.b.double^(\*) b$ then $b$ is well-typed.] <thm:type-safety>
#block[Evaluation does not block. That is, for any
  partial evaluation $a arrow.b.double^(\*) b$, where $a$ is well-typed,
  the derivation can be extended.] <thm:progress-denotational>
==== In-place update & typestate
<in-place-update-typestate>
Furthermore, linear types can be used to implement some operations as
in-place updates, and typestates (like whether an array is mutable or
frozen) are actually enforced by the type system.

To prove this, we introduce a second, distinct, semantics. It is also a
Launchbury-style semantics. It differs from
#cite(<launchbury_natural_1993>, form: "prose") in the following ways:

- Environments are enriched with mutable references (for the sake of
  concreteness, they are all references to arrays but they could be
  anything).

- Typestates are implemented by mutating the type of such references,
  functions can block if the type of the references is not correct: that
  is, we track typestates dynamically.

The idea behind the latter is that progress will show that we are never
blocked by typestates. In other words, they are enforced statically and
can be erased at runtime.

It is hard to reason on a lazy language with mutation. But what we show
is that we are using mutation carefully enough so that they behave as
pure data. To formalise this, we relate this semantics with mutation to
our pure semantics above. Specifically, we show that they are
#emph[bisimilar];. #cite(<amani_cogent_2016>, form: "prose") use a
similar technique for a language with linear types and both a pure and
imperative semantics.

Bisimilarity allows us to lift the type-preservation and progress from
the pure semantics. That is, writing $sigma \, tau$ for states of this
evaluation with mutation:

#block[For any well-typed $sigma$, if
  $sigma arrow.b.double tau$ or $sigma arrow.b.double^(\*) tau$, then
  $tau$ is well-typed.] <thm:type-preservation>
#block[Evaluation does not block. That is, for any partial
  evaluation $sigma arrow.b.double^(\*) tau$, for $sigma$ well-typed, the
  evaluation can be extended. In particular, typestates need not be
  checked dynamically.] <thm:progress>
Just as importantly, we can prove that, indeed, we cannot observe
mutations. More precisely, we prove that the pure semantics and the
semantics with mutation are observationally equivalent: any observation,
which we reduce to a boolean test, is identical in either semantics.

#block[The semantics with in-place mutation is observationally
  equivalent to the pure semantics.

  That is, for any closed term of type $sans("Bool")$, if $e$ evaluates to
  the value $z$ with the pure semantics, and to the value $z'$ with the
  semantics with mutation, then $z = z'$.] <thm:obs-equiv>
== Design choices & trade-offs
<sec:design-choices>
We could as well have picked different points in the design space for
$lambda_arrow.r^q$. We review some of the choices we made in this
section.

==== Case rule
<case-rule>
Thanks to $sans("case")_omega$, we can use linear arrows on all data
types. Indeed we can write the following and have $sans("fst")$ typecheck:
```haskell
data Pair a b where
  Pair :: a ⊸ b ⊸ Pair a b
fst :: Pair a b -> a
fst x = caseω x of Pair a b -> a
```
It is possible to do without $sans("case")_omega$, and have only
$sans("case")_1$. Consider $sans("fst")$ again. We could instead have:
```haskell
data Pair p q a b where
  Pair :: a ->p b ->q Pair p q a b
fst :: Pair 1 ω a b ⊸ a
fst x = case1 x of Pair a b -> a
```
But now multiplicity polymorphism infects all basic datatypes (such
as pairs), with knock-on consequences. Moreover, $bold("let")$
is annotated so it seems reasonable to annotate $bold("case")$
in the same way.

To put it another way, $sans("case")_omega$ allows us to meaningfully
inhabit
$forall sans(a) sans(b) . sans("Unrestricted") \( sans(a) \, sans(b) \) multimap \( sans("Unrestricted") sans(a) \, sans("Unrestricted") sans(b) \)$,
while linear logic does not.

==== Subtyping
<subtyping>
Because the type $A multimap B$ only strengthens the contract of its
elements compared to $A arrow.r B$, one might expect the type
$A multimap B$ to be a subtype of $A arrow.r B$. But while
$lambda_arrow.r^q$ has #emph[polymorphism];, it does not have
#emph[subtyping];. For example, if:
```haskell
f :: Int ⊸ Int
g :: (Int -> Int) -> Bool
```
then the call $\( sans(g) sans(f) \)$ is ill-typed, even
though $sans(f)$ provides more guarantees than $sans(g)$ requires. On
the other hand, $sans(g)$ might well be multiplicity-polymorphic, with
type
$forall sans(p) . \( sans("Int") arrow.r_(sans(p)) sans("Int") \) arrow.r sans("Bool")$;
in which case $\( sans(g) sans(f) \)$ is, indeed, typeable.

The lack of subtyping is a deliberate choice in our design: it is well
known that Hindley-Milner-style type inference does not mesh well with
subtyping (see, for example, the extensive exposition by
#cite(<pottier_subtyping_1998>, form: "prose");, but also
#cite(<dolan_mlsub_2017>, form: "prose") for a counterpoint).

However, while $\( sans(g) sans(f) \)$ is ill-typed in
$lambda_arrow.r^q$, it is accepted in Linear Haskell. The reason is that
the $eta$-expansion
$sans(g) \( lambda sans(x) arrow.r sans(f) sans(x) \)$
#emph[is] typeable, and Linear Haskell perform this expansions during
type inference. Such an $eta$-expansion is not completely
semantics-preserving as $lambda sans(x) arrow.r sans(g) sans(x)$
is always a well-defined value, even if $sans(g)$ loops: this difference
can be observed with Haskell's $sans("seq")$ operator. Nevertheless, such
$eta$-expansions are already standard practice in #smallcaps[ghc];: a
similar situation arises when using rank-2 types. For example, the core
language of #smallcaps[ghc] does not accept $sans(g) sans(f)$
for:
```haskell
g :: (∀a. (Eq a, Show a) => a -> Int) -> Char
f :: ∀a. (Show a, Eq a) => a -> Int
```
The surface language, again, accepts $sans(g) sans(f)$,
and elaborates it into
$sans(g) \( lambda sans(a) \( sans("d1") : : sans("Eq") sans(a) \) \( sans("d2") : : sans("Show") sans(a) \) arrow.r sans(f) sans(a) sans("d2") sans("d1") \)$.
We simply extend this mechanism to linear types.

==== Polymorphism & multiplicities
<polymorphism-multiplicities>
Consider the definition: "$sans("id") sans(x) = sans(x)$". Our
typing rules would validate both
$sans("id") : : sans("Int") arrow.r sans("Int")$ and
$sans("id") : : sans("Int") multimap sans("Int")$. So, since we think of
multiplicities ranging over ${ 1 \, omega }$, surely we should also have
$sans("id") : : forall sans(p) . sans("Int") arrow.r_(sans(p)) sans("Int")$?
But as it stands, our rules do not accept it. To do so we would need
$x :_p "Int" tack.r x : "Int"$. Looking at the (var) rule in Fig. 6, we can
prove that premise by case analysis, trying $p = 1$ and $p = omega$. But
if we had a domain of multiplicities which includes $0$ (see Sec. 7.2), we would
not be able to prove $x :_p "Int" tack.r x : "Int"$, and rightly so
because it is not the case that
$sans("id") : : sans("Int") arrow.r_(upright(0)) sans("Int")$.

More generally, we could type more programs if we added more laws
relating variables in Def. 3.4, such as $p + q = omega$, but this would prevent
potential extensions to the set of multiplicities. For now, we accept
the more conservative rules of Def. 3.4.

==== Divergence.
<divergence.>
Consider this definition#footnote[$\( sans("repeat") sans(x) \)$
  returns the infinite list $\[ sans(x) \, sans(x) \, . . . \]$. The
  function (++) appends two lists, and
  has type $\[ sans(a) \] multimap \[ sans(a) \] multimap \[ sans(a) \]$;
  we have not given a formal typing rule for recursive definitions, but
  its form is entirely standard.];:
```haskell
f :: [Int] ⊸ [Int]
f xs = repeat 1 ++ xs
```
But wait! Does $sans(f)$ #emph[really] consume its argument $sans("xs")$
exactly once? After all, $\( sans("repeat") upright(1) \)$ is
infinite so $sans(f)$ will never evaluate $sans("xs")$ at all!

In corner cases like this we look to metatheory. Yes, the typing rules
give the specified types for (++) and
$sans(f)$. Yes, the operational claims guaranteed by the metatheory
remain valid. Intuitively you may imagine it like this: linearity claims
that #emph[if] you were consume the result of $sans(f)$ completely,
exactly once, then you would consume its argument once; but since the
result of $sans(f)$ is infinite we cannot consume it completely exactly
once, so the claim holds vacuously.

= Implementing Linear Haskell
<sec:implementation>

We implement Linear Haskell on top of the leading Haskell compiler,
#smallcaps[ghc];, version
8.2#footnote[https:\/\/github.com/tweag/ghc/tree/linear-types];. The
implementation modifies type inference and type-checking in the
compiler. Neither the intermediate language~@sulzmann_fc_2007 nor the
run-time system are affected. Our implementation of multiplicity
polymorphism is incomplete, but the current prototype is sufficient for
the examples and case studies presented in in this paper (see Sec. 5).

In order to implement the linear arrow, we added a multiplicity
annotation to function arrows as in $lambda_arrow.r^q$. The constructor
for arrow types is constructed and destructed frequently in
#smallcaps[ghc];'s type checker, and this accounts for most of the
modifications to existing code.

As suggested in Sec. 3.2, the multiplicities are an output of the type inference
algorithm. In order to infer the multiplicities coming out of a
$bold("case")$ expression we need a way to aggregate the
multiplicities coming out of the individual branches. To this effect, we
compute, for every variable, the join of its multiplicity in each
branch.

Implementing Linear Haskell affects 1,152 lines of #smallcaps[ghc] (in
subsystems of the compiler that together amount to more than 100k lines
of code), including 444 net extra lines. These figures support our claim
that Linear Haskell is easy to integrate into an existing
implementation: despite #smallcaps[ghc] being 25 years old, we implement
a first version of Linear Haskell with reasonable effort.

= Evaluation and Case Studies
<sec:evaluation>

While many linear type systems have been proposed, a #emph[retrofitted]
linear type system for a mature language like Haskell offers the
opportunity to implement non-trivial applications mixing linear and
non-linear code, I/O, etc., and observe how linear code interacts with
existing libraries and the optimiser of a sophisticated compiler.

Our first method for evaluating the implementation is to simply compile
a large existing code base together with the following changes: (1) all
(non-#smallcaps[gadt];) data constructors are linear by default, as
implied by the new type system; and (2) we update standard list
functions to have linear types ($++$,
$sans("concat")$, $sans("uncons")$). Under these conditions, we verified
that the base #smallcaps[ghc] libraries and the nofib benchmark suites
compile successfully: 195K lines of Haskell, providing preliminary
evidence of backwards compatibility.

In the remainder of section, we describe case-studies implementated with
the modified #smallcaps[ghc] of Sec. 4. In Sec. 7.3, we propose further applications
for Linear Haskell, which we have not yet implemented, but which
motivate this work.

== Computing directly with serialised data
<sec:cursors>
While Sec. 2.2 covered simple mutable arrays, we now turn to a related but more
complicated application: operating directly on binary, serialised
representations of algebraic datatypes (like
#cite(<vollmer_gibbon_2017>, form: "prose") do). The motivation is that
programs are increasingly decoupled into separate (cloud) services that
communicate via serialised data in text or binary formats, carried by
remote procedure calls. The standard approach is to deserialise data
into an in-heap, pointer-based representation, process it, and then
serialise the result for transmission. This process is inefficient, but
nevertheless tolerated, because the alternative --- computing directly
with serialised data --- is far too difficult to program. Nevertheless,
the potential performance gain of working directly with serialised data
has motivated small steps in this direction: libraries like "Cap'N
Proto"~#footnote[#link("https://capnproto.org/");] enable unifying
in-memory and on-the-wire formats for simple product types (protobufs).

Here is an unusual case where advanced types can yield
#emph[performance] by making it practical to code in a previously
infeasible style: accessing serialised data at a fine grain without
copying it.

```haskell
data Tree = Leaf Int | Branch Tree Tree
pack :: Tree ⊸ Packed ′[Tree]
unpack :: Packed ′[Tree] ⊸ Tree
caseTree :: Packed (Tree ′: r) ->p
  (Packed (Int ′: r) ->p a) ->
  (Packed (Tree ′: Tree ′: r) ->p a) -> a
```
The interface on the right gives an example of type-safe,
#emph[read-only] access to serialised data for a particular
datatype#footnote[This interface uses type-level lists as can be found
  in Haskell's DataKind extension];. A $sans("Packed")$ value is a pointer
to raw bits (a bytestring), indexed by the types of the values contained
within. We define a #emph[type-safe] serialisation layer as one which
#emph[reads] byte-ranges only at the type and size they were originally
#emph[written];. This is a small extension of the memory safety we
already expect of Haskell's heap --- extended to include the contents of
bytestrings containing serialised data#footnote[The additional safety
  ensured here is lower-stakes than typical memory-safety, as, even it is
  violated, the serialised values do not contain pointers and cannot
  segfault the program reading them.];. To preserve this type safety, the
$sans("Packed")$ type #emph[must] be abstract. Consequently, a client of
the module defining $sans("Tree")$ need not be privy to the memory layout
of its serialisation.

If we cannot muck about with the bits inside a $sans("Packed")$ directly,
then we can still retrieve data with $sans("unpack")$, #emph[i.e.];, the
traditional, #emph[copying];, approach to deserialisation. Better still
is to read the data #emph[without] copying. We can manage this feat with
$sans("caseTree")$, which is analogous to the expression
"$bold("case") sans(e) bold("of") { sans("Leaf") . . . ; sans("Branch") . . . }$".
Lacking built-in syntax,
$\( sans("caseTree") sans(p) sans("k1") sans("k2") \)$
takes two continuations corresponding to the two branches of the case
expression. Unlike the case expression, $sans("caseTree")$ operates on the
packed byte stream, reads a tag byte, advances the pointer past it, and
returns a type-safe pointer to the fields
(#emph[e.g.];$sans("Packed")' \[ sans("Int") \]$ in the case of a leaf).

It is precisely to access multiple, consecutive fields that
$sans("Packed")$ is indexed by a #emph[list] of types as its phantom type
parameter. Individual atomic values ($sans("Int")$, $sans("Double")$, etc)
can be read one at a time with a lower-level $sans("read")$ primitive,
which can efficiently read out scalars and store them in registers:
```haskell
read :: Storable a => Packed (a ′: r) ⊸ (a, Packed r)
```

```haskell
sumLeaves :: Packed ′[Tree] -> Int
sumLeaves p = fst (go p)
  where go p = caseTree p
          read -- Leaf case
          (λp2 -> let (n, p3) = go p2
                      (m, p4) = go p3
                  in (n + m, p4))
```
Putting it together, we can write a function that consumes serialised
data, such as $sans("sumLeaves")$, shown on the right. Indeed, we can even
use $sans("caseTree")$ to implement $sans("unpack")$, turning it into safe
"client code" -- sitting outside the module that defines $sans("Tree")$
and the trusted code establishing its memory representation.

In this read-only example, linearity was not essential, only phantom
types. Next we consider an #smallcaps[API] for writing
$sans("Packed")' \[ sans("Tree") \]$ values bit by bit, where linearity is
key. In particular, can we also implement $sans("pack")$ using a public
interface?

=== Writing serialised data
<writing-serialised-data>
To create a serialised data constructor, we must write a tag, followed
by the fields. A #emph[linear] write pointer can ensure all fields are
initialised, in order. We use a type "$sans("Needs")$" for write pointers,
parameterised by (1) a list of remaining things to be written, and (2)
the type of the final value which will be initialised once those writes
are performed. For example, after we write the tag of a $sans("Leaf")$ we
are left with: "$sans("Needs")' \[ sans("Int") \] sans("Tree")$" ---
an #emph[obligation] to write the $sans("Int")$ field, and a
#emph[promise] to receive a $sans("Tree")$ value at the end (albeit a
packed one).

To write an individal number, we provide a primitive that shaves one
element off the type-level list of obligations (a counterpart to
$sans("read")$, above): As with mutable arrays, this $sans("write")$
operates in-place on the buffer, in spite being a pure function.
```haskell
write :: Storable a => a ⊸ Needs (a ′: r) t ⊸ Needs r t
```
When the list of outstanding writes is empty, we can retrive a readable
packed buffer. Just as when we froze arrays (Sec. 2.2), the immutable value is
#emph[unrestricted];, and can be used multiple times:
```haskell
finish :: Needs ′[ ] t ⊸ Unrestricted (Packed ′[t])
```
Finalizing written values with $sans("finish")$ works hand in hand with
allocating new buffers in which to write data (similar to
$sans("newMArray")$ from Sec. 2.2):
```haskell
newBuffer :: (Needs ′[a] a ⊸ Unrestricted b) ⊸ b
```
We also need to explicitly let go of
linear input buffers we've exhausted.
```haskell
done :: Packed ′[ ] ⊸ ()
```

The primitives $sans("write")$, $sans("read")$, $sans("newBuffer")$,
$sans("done")$, and $sans("finish")$ are #emph[general] operations for
serialised data, whereas $sans("caseTree")$ is datatype-specific. Further,
the module that defines $sans("Tree")$ exports a datatype-specific way to
#emph[write] each serialised data constructor:
```haskell
startLeaf :: Needs (Tree ′: r) t ⊸ Needs (Int ′: r) t
startBranch :: Needs (Tree ′: r) t ⊸ Needs (Tree ′: Tree ′: r) t
```
Operationally, $sans("start") \*$ functions write only the tag,
hiding the exact tag-encoding from the client, and leaving field-writes
as future obligations. With these building blocks, we can move
$sans("pack")$ and $sans("unpack")$ outside of the private code that defines
$sans("Tree")$s, which has this minimal interface:
```haskell
module TreePrivate (Tree (. .), caseTree, startLeaf, startBranch)
module Data.Packed (Packed, Needs, read, write, newBuffer, finish, done)
```
On top of the safe interface, we can of course define
higher-level construction routines, such as for writing a complete
$sans("Leaf")$:
```haskell
writeLeaf n = write n ◦ startLeaf
```
Now we can allocate and initialize a complete tree ---
equivalent to
$sans("Branch") \( sans("Leaf") upright(3) \) \( sans("Leaf") upright(4) \)$,
but without ever creating the non-serialised values --- as follows:
```haskell
newBuffer (finish ◦ writeLeaf 4 ◦ writeLeaf 3 ◦ startBranch) :: Packed ′[Tree]
```

Finally, we have what we need to build a map function that logically
operates on the leaves of a tree, but reads serialised input and writes
serialised output. Indeed, in our current Linear Haskell implementation
"$sans("mapLeaves") \( + upright(1) \) sans("tree")$"
touches #emph[only] packed buffers --- it performs zero Haskell heap
allocation! We will return to this map example and benchmark it in Sec. 5.1.3.
With the safe interface to serialised data, functions like
$sans("sumLeaves")$ and $sans("mapLeaves")$ are not burdensome to program.
The code for $sans("mapLeaves")$ is shown below.

```haskell
mapLeaves :: (Int -> Int) -> Packed ′[Tree] ⊸ Packed ′[Tree]
mapLeaves fn pt = newBuffer (extract ◦ go pt)
  where
    extract (inp, outp) = case done inp of () -> finish outp
    go :: Packed (Tree ′: r) ⊸ Needs (Tree ′: r) t ⊸ (Packed r, Needs r t)
    go p = caseTree p (λp o -> let (x, p') = read p in (p', writeLeaf (fn x) o))
                      (λp o -> let (p', o') = go p (writeBranch o) in go p' o')
```

=== A version without linear types
<sec:st-cursors>
How would we build the same thing in Haskell without linear types? It
may appear that the ST monad is a suitable choice:

```haskell
writeST :: Storable a => a -> Needs' s (a ′: r) t -> ST s (Needs' s r t)
```
Here we use the same typestate associated with a $sans("Needs")$
pointer, while also associating its mutable state with the $sans("ST")$
session indexed by $sans(s)$. Unfortunately, not only do we have the
same trouble with freezing in the absence of linearity
($sans("unsafeFreeze")$, Sec. 2.2), we also have an #emph[additional] problem not
present with arrays: namely, a non-linear use of a $sans("Needs")$ pointer
can ruin our type-safe deserialisation guarantee! For example, we can
write a $sans("Leaf")$ and a $sans("Branch")$ to the same pointer in an
interleaved fashion. Both will place a tag at byte 0; but the leaf will
place an integer in bytes 1-9, while the branch will place another tag
at byte 1. We can receive a corrupted 8-byte integer, clobbered by a tag
from an interleaved "alternate future".

Fixing this problem would require switching to an indexed monad with
additional type-indices that model the typestate of all accessible
pointers, which would in turn need to have static, type-level
identifiers. That is, it would require #emph[encoding] linearity after
all, but in a way which would become very cumbersome as soon as several
buffers are involved.

=== Benchmarking compiler optimisations
<sec:cursor-benchmark>
#figure(
  [#block[
    #include "figures/sumtree_all_plot_baseline_unpack-repack.typ"
    #include "figures/maptree_plot_baseline_unpack-repack.typ"
  ]],
  caption: [
    Speedup of operating directly on serialised data, either using
    linear-types or the ST monad, as compared to fully unpacking,
    processing, and repacking the data. For reference, a "pointer-based"
    version is also included, which doesn't operate on serialised data
    at all, but instead normal heap objects --- it represents the
    hypothetical performance of "unpack-repack" if (de)serialisation
    were instantaneous.
  ],
)
<fig:pack-bench>

Finally, as shown in Fig. 7, there are some unexpected performance
consequences from using a linear versus a monadic, ST style in
#smallcaps[ghc];. Achieving allocation-free loops in #smallcaps[ghc] is
always a challenge --- tuple types and numeric types are lazy and
"boxed" as heap objects by default. As we saw in the $sans("sumLeaves")$
and $sans("mapLeaves")$ examples, each recursive call returned a tuple of
a result and a new pointer. In a monadic formulation, an expression of
type $sans(m) sans(a)$, for $sans("Monad") sans(m)$,
implies that the "result" type $sans(a)$, of kind $\*$, must be a
#emph[lifted] type. Nevertheless, in some situations, for some monads,
the optimiser is able to deforest data constructors returned by monadic
actions. In the particular case of $sans("fold")$ and $sans("map")$
operations over serialised trees, unfortunately, we are currently unable
to eliminate all allocation from $sans("ST")$-based implementations of the
algorithms.

For the linearly-typed code, however, we have more options.
#smallcaps[ghc] has the ability to directly express unboxed values such
as a tuple $\( \# sans("Int") \# \, sans("Double") \# \# \)$, which fills
two registers and inhabits an unboxed kind distinct from $\*$. In fact,
the type of a combinator like $sans("caseTree")$ is a good fit for the
recent "levity polymorphism" addition to
#smallcaps[ghc];~@eisenberg_levity_2017. Thus we permit the branches of
the $bold("case")$ to return unlifted, unboxed types, and give
$sans("caseTree")$ a more general type:
```haskell
caseTree :: ∀(rep :: RuntimeRep) (res :: TYPE rep) b.
  Packed (Tree ′: b) ->p (Packed (Int ′: b) ->p res) -> (Packed (Tree ′: Tree ′: b) ->p res) -> res
```
This works because we do not need to #emph[call] a
function with $sans("res")$ as argument (and thus unknown calling
conventions) only return it. Using this approach, we were able to ensure
by construction that the "linear/packed" implementations in Fig. 7 were
completely non-allocating, rather than depending on the optimiser. This
results in better performance for the linear, compared to monadic
version of the serialised-data transformations.

The basic premise of Fig. 7 is that a machine in the network receives,
processes, and transmits serialized data (trees). We consider two simple
benchmarks: $sans("sumLeaves")$ and
$sans("mapTree") \( + upright(1) \)$. The baseline is the
traditional approach: deserialise, transform, and reserialise, the
"unpack-repack" line in the plots. Compared to this baseline,
#emph[processing the data directly in its serialised form results in
  speedups of over 20$times$ on large trees];. What linear types makes
safe, is also efficient.

The experiment was conducted on a Xeon E5-2699 CPU (2.30GHz, 64GB
memory) using our modified version of #smallcaps[ghc] 8.2 (Sec. 4). Each data
point was measured by performing many trials and taking a linear
regression of iteration count against time#footnote[using the criterion
  library~@osullivan_criterion_2013];. This process allows for accurate
measurements of both small and large times. The baseline unpack-repack
tree-summing times vary from 25ns to 1.9 seconds at depths 1 and 24
respectively. Likewise, the baseline mapping times vary from 215ns to
2.93 seconds. We use a simple contiguous implementation of buffers for
serialisation#footnote[A full, practical implementation should include
  growable or doubling buffers.];. At depth 20, one copy of the tree takes
around 10MB, and towards the right half of the plot we see tree size
exceeding cache size.

== Sockets with type-level state
<sec:sockets>
The #smallcaps[bsd] socket #smallcaps[api] is a standard, if not
#emph[the] standard, through which computers connect over networks. It
involves a series of actions which must be performed in order: on the
server-side, a freshly created socket must be #emph[bound] to an
address, then start #emph[listening] incoming traffic, then
#emph[accept] connection requests; said connection is returned as a new
socket, this new socket can now #emph[receive] traffic. One reason for
having that many steps is that the precise sequence of actions is
protocol-dependent. For #smallcaps[tcp] traffic you would do as
described, but for #smallcaps[udp];, which does not need connections,
you would not accept a connection but receive messages directly.

The `socket` library for Haskell, exposes precisely this sequence of
actions. Programming with it is exactly as clumsy as socket libraries
for other languages: after each action, the state of the socket changes,
as do the permissible actions, but these states are invisible in the
types. Better is to track the state of sockets in the type, akin to a
typestate analysis~@strom_typestate_1983. In the $sans("File")$
#smallcaps[api] of Sec. 2.3, we made files safer to use at the cost of having to
thread a file handle explicitely: each function consumes a file handle
and returns a fresh one. We can make this cost into an opportunity: we
have the option of returning a handle with a _different_ type from that
of the handle we consumed! So by adjoining a phantom type to sockets to
track their state, we can effectively encode the proper sequencing of
socket actions.

As an illustration, we implemented wrapper around the #smallcaps[api] of
the socket library. For concision, this wrapper is specialised for the
case of #smallcaps[tcp];.

```haskell
data State = Unbound | Bound | Listening | Connected
data Socket (s :: State)
data SocketAddress
socket :: IOL 1 (Socket Unbound)
bind :: Socket Unbound ⊸ SocketAddress -> IOL 1 (Socket Bound)
listen :: Socket Bound ⊸ IOL 1 (Socket Listening)
accept :: Socket Listening ⊸ IOL 1 (Socket Listening, Socket Connected)
connect :: Socket Unbound ⊸ SocketAddress -> IOL 1 (Socket Connected)
send :: Socket Connected ⊸ ByteString -> IOL 1 (Socket Connected, Unrestricted Int)
receive :: Socket Connected ⊸ IOL 1 (Socket Connected, Unrestricted ByteString)
close :: ∀s. Socket s -> IOL ω ()
```

This linear socket #smallcaps[api] is very similar to that of files: we
use the $sans("IO")_(sans(L))$ monad in order to enforce linear use of
sockets. The difference is the argument to $sans("Socket")$, which
represents the current state of the socket and is used to limit the
functions which apply to a socket at a given time.

==== Implementing the linear socket #smallcaps[api];.
<implementing-the-linear-socket-api.>
Our socket #smallcaps[api] has been tested by writing a small
echo-server. The #smallcaps[api] is implemented as a wrapper around the
socket library. Each function wrapped takes half-a-dozen lines of code,
of type annotation and coercions between $sans("IO")$ and
$sans("IO")_(sans(L))$#footnote[Since our implementation of Linear Haskell
  does not yet have multiplicity-polymorphism, we had to fake it with type
  families and #smallcaps[gadt];s];. There is no computational behaviour
besides error recovery.

It would have been too restrictive to limit the typestate to enforce the
usage protocol of #smallcaps[tcp];. We do not intend for a new set of
wrapper functions to be implemented for each protocol. Instead the
wrappers are implemented with a generic type-state evolving according to
the rules of a deterministic automaton. Each protocol can define it's
own automaton, which is represented as a set of instances of a type
class.

== Pure bindings to impure #smallcaps[apis]
<sec:spritekit>
In Haskell SpriteKit, #cite(<chakravarty_haskell_2017>, form: "prose")
have a different kind of problem. They build a pure interface for
graphics, in the same style as the Elm programming
language~@czaplicki_elm_2012, but implement it in terms of an existing
imperative graphical interface engine.

Basically, the pure interface takes an update function
$sans(u) : sans("Scene") arrow.r sans("Scene")$ which is tasked with
returning the next state that the screen will display. The scene is
first converted to a pure tree where each node keeps, along with the pure
data, a pointer to its imperative counterpart when it applies, or
$sans("Nothing")$ for new nodes.
```haskell
data Node = Node {payload :: Int, ref :: Maybe (IORef ImperativeNode), children :: [Node]}
```

On each frame, SpriteKit applies $sans(u)$ to the current scene, and
checks if a node $sans(n)$ was updated. If it was, it applies the update
directly onto $sans("ref") sans(n)$ or creates a new imperative
node.

Things can go wrong though: if the update function #emph[duplicates] any
proxy node, one gets the situation where two nodes $sans(n)$ and
$sans("n'")$ can point to the same imperative source
$sans("ref") sans(n) = sans("ref") sans("n'")$, but have
different payloads. In this situation the $sans("Scene")$ has become
inconsistent and the behaviour of SpriteKit is unpredictable.

In the #smallcaps[api] of
#cite(<chakravarty_haskell_2017>, form: "prose");, the burden of
checking non-duplication is on the programmer. Using linear types, we
can switch that burden to the compiler: we change the update function to
type $sans("Scene") multimap sans("Scene")$, and the $sans("ref")$ field is
made linear too. Thanks to linearity, no reference can be duplicated: if
a node is copied, the programmer must choose which one will correspond
to the old imperative counterpart and which will be new.

We implemented such an #smallcaps[api] in our implementation of Linear
Haskell. The library-side code does not use any linear code, the
$sans("Node")$s are actually used unrestrictedly. Linearity is only
imposed on the user of the interface, in order to enforced the above
restriction.

= Related work
<sec:related>
== Linearity via arrows vs. linearity via kinds
<sec:kinds>
There are two possible choices to indicate the distinction between
linear and unrestricted objects. Our choice is to use the arrow type.
That is, we have both a linear arrow to introduce linear objects in the
environment, and an unrestricted arrow to introduce unrestricted
objects. This choice is featured in the work of
#cite(<mcbride_rig_2016>, form: "prose") and
#cite(<ghica_bounded_2014>, form: "prose") and is ultimately inspired by
Girard's presentation of linear logic, which features only linear
arrows, and where the unrestricted arrow $A arrow.r B$ is encoded as
$! A multimap B$.

Another popular choice
@wadler_linear_1990; @mazurak_lightweight_2010; @tov_practical_2011; @morris_best_2016
is to separate types into two kinds: a linear kind and an unrestricted
kind. Values with a type whose kind is linear are linear, and the others
are unrestricted. (Thus in particular such systems feature "linear
arrows", but they have a completely different interpretation from ours.)
While this does not match linear logic (there is no such thing as a
linear proposition), it is attractive on the surface because,
intuitively, some types are inherently linear (file handles, updateable
arrays, etc.) and some types are inherently unrestricted ($sans("Int")$,
$sans("Bool")$, etc.). However, after scratching the surface we have
discovered that "linearity via arrows" has an edge over "linearity via
kinds".

==== Better code reuse.
<better-code-reuse.>
When retrofitting linear types in an existing language, it is important
to share as much code as possible between linear and non-linear code. In
a system with linearity on arrows, the subsumption relation (linear
arrows subsume unrestricted arrows) and the scaling of context in the
application rule mean that much linear code can be used as-is from
unrestricted code, and be properly promoted. Indeed, assuming lists as
defined in Sec. 2.4 and:
```haskell
(++) :: [a] ⊸ [a] ⊸ [a] -- Append two lists
cycle :: [a] -> [a]      -- Repeat a list, infinitely
```
The following definition type-checks, even though $++$ is applied to
unrestricted values and used in an unrestricted context:
```haskell
f :: [a] -> [a] -> [a]
f xs ys = cycle (xs ++ ys)
```
In contrast, in a two-kind system, a function must declare the #emph[exact]
linearity of its return value. Consequently, to make a function
promotable from linear to unrestriced, its declaration must use
polymorphism over kinds.

As seen in Sec. 2, in Linear Haskell reuse of linear code extends to datatypes:
the usual parametric datatypes (lists, pairs, etc.) work both with
linear and unrestricted values. On the contrary, if linearity depends on
the kind, then if a linear value is contained in a type, the container
type must be linear too. (Indeed, an unrestricted container could be
discarded or duplicated, and its contents with it.) Consequently,
sharing data types also requires polymorphism. For example, in a
two-kinds system, the $sans("List")$ type may look like so, if one
assumes a that $sans("Type") upright(1)$ is the kind of linear
types and $sans("Type") omega$ is the kind of unrestricted types:
```haskell
data List (p :: Multiplicity) (a :: Type p) :: Type p = [ ] | a : (List p m a)
```
The above declaration ensures that the linearity of the list inherits
the linearity of the contents. A linearity-polymorphic
(++) function could have the
definition:
```haskell
(++) :: List p a -> List p a -> List p a
[ ] ++ xs = xs
(x : xs) ++ ys = x : (xs ++ ys)
```
Compared to our append function, the type of the above requires
multiplicity polymorphism $sans(p)$. Additionnally, the above function
cannot (and should not) mix linear and unrestricted lists. Indeed
because multiplicity is attached to the type of elements it must be the
same for both arguments and the returned value.

Note that, in the above, we parameterize over multiplicities instead of
parameterizing over kinds directly, as is customary in the literature.
We do so because it fits better #smallcaps[ghc];, whose kinds are
already parameterized over a so-called levity~@eisenberg_levity_2017.

==== ATS.
<ats.>
The ATS language has a unique take on linear types~@zhu_safe_2005, which
can be classified as linearity via kinds and does not have
polymorphism.ATS has a notion of stateful views: views are linear
values without run-time representation and are meant to track the state
of pointers (#emph[e.g.] whether they are initialised). Pointers
themselves remain unrestricted values: only views are linear.

==== Dependent types.
<dependent-types.>
Linearity on the arrow meshes better with dependent types (see Sec. 7.2). Indeed,
consider a typical predicate over files
($sans(P) : sans("File") arrow.r \*$). It may need to mention its argument
several times to relate several possible sequences of operations on the
file. While this is not a problem in our system, the function $sans(P)$
is not expressible if $sans("File")$ is intrinsically linear. Leaving the
door open to dependent types is crucial to us, as this is currently
explored as a possible extension to
#smallcaps[ghc]~@weirich_specification_2017.

==== Linear values.
<linear-values.>
Yet, an advantage of "linearity via kinds" is the possibility to
directly declare the linearity of values returned by a function -- not
just that of the argument of a function. In contrast, in our system if
one wants to indicate that a returned value is linear, we have to use a
double-negation trick. That is, given
$f : A arrow.r \( B multimap ! r \) multimap r$, then $B$ can be used a
single time in the (single) continuation, and effectively $f$ "returns"
a single $B$. One can obviously declare a type for linear values
$sans("Linear") sans(a) = \( sans(a) multimap ! sans(r) \) multimap sans(r)$
and chain $sans("Linear")$-returning functions with appropriate
combinators. In fact, as explained in Sec. 2.7, the cost of the double
negation almost entirely vanishes in the presence of an ambient monad.

== Other variants of "linearity on the arrow"
<other-variants-of-linearity-on-the-arrow>
The $lambda_arrow.r^q$ type system is heavily inspired from the work of
#cite(<ghica_bounded_2014>, form: "prose") and
#cite(<mcbride_rig_2016>, form: "prose");. Both of them present a type
system where arrows are annotated with the multiplicty of the the
argument that they require, and where the multiplicities form a
semi-ring.

In contrast with $lambda_arrow.r^q$, McBride uses a
multiplicity-annotated type judgement $Gamma tack.r_rho t : A$, where
$rho$ represents the multiplicity of $t$. So, in McBride's system, when
an unrestricted value is required, instead of computing $omega Gamma$,
it is enough to check that $rho = omega$. The problem is that this check
is arguably too coarse, and results in the judgement
$tack.r_omega lambda x . \( x \, x \) : A multimap \( A \, A \)$ being
derivable. This derivation is not desirable: it implies that there
cannot be reusable definitions of linear functions. In terms of linear
logic~@girard_linear_1987, McBride makes the natural function of type
$! \( A multimap B \) arrow.r.double ! A multimap ! B$ into an
isomorphism. In that respect, our system is closer to Ghica and Smith's.

The essential differences between our system and that of Ghica and
Smith is that we support multiplicity-polymorphism and datatypes. In
particular our $sans("case")$ rule is novel.

The literature on so-called
coeffects~@petricek_coeffects_2013; @brunel_core_2014 uses type systems
similar to Ghica and Smith, but with a linear arrow and multiplicities
carried by the exponential modality instead. Brunel et al. [2014], in
particular, develops a Krivine-style realisability model for such a
calculus. We are not aware of an account of Krivine realisability for
lazy languages, hence this work is not directly applicable to
$lambda_arrow.r^q$.

== Uniqueness and ownership typing
<sec:uniqueness>
The literature contains many proposals for uniqueness (or ownership)
types (in contrast with linear types). Prominent representative
languages with uniqueness types include
Clean~@barendsen_uniqueness_1996 and Rust~@matsakis_rust_2014. Linear
Haskell, on the other hand, is designed around linear types based on
linear logic~@girard_linear_1987.

Idris~@brady_idris_2013 features uniqueness types, which have been
used, in particular, to enforce communication
protocols~@brady_type-driven_2017. Uniqueness types, in Idris, are being
replaced by linear types based on QTT~@atkey_syntax_2017, a variant of
McBride~@mcbride_rig_2016.

Linear types and uniqueness types are, at their core, dual: whereas a
linear type is a contract that a function uses its argument exactly once
even if the call's context can share a linear argument as many times as
it pleases, a uniqueness type ensures that the argument of a function is
not used anywhere else in the expression's context even if the callee
can work with the argument as it pleases. Seen as a system of
constraints, uniqueness typing is a #emph[non-aliasing] analysis while
linear typing provides a #emph[cardinality] analysis. The former aims at
in-place updates and related optimisations, the latter at inlining and
fusion. Rust and Clean largely explore the consequences of uniqueness on
in-place update; an in-depth exploration of linear types in relation
with fusion can be found in
#cite(<bernardy_composable_2015>, form: "prose"); see also the
discussion in Sec. 7.1.

Because of this weak duality, we could have retrofitted uniqueness types
to Haskell. But several points guided our choice of designing Linear
Haskell around linear logic instead: (a) functional languages have more
use for fusion than in-place update (if the fact that #smallcaps[ghc] has
a cardinality analysis but no non-aliasing analysis is any indication);
(b) there is a wealth of literature detailing the applications of
linear logic --- see Sec. 5; (c) and decisively, linear type systems are
conceptually simpler than uniqueness type systems, giving a clearer path
to implementation in #smallcaps[ghc];.

==== Rust & Borrowing.
<rust-borrowing.>
In Linear Haskell we need to thread linear variables throughout the
program. Even though this burden could be alleviated using syntactic
sugar, Rust uses instead a type-system feature for this purpose:
#emph[borrowing];. Borrowed values differ from owned values in that they
can be used in an unrestricted fashion, albeit in a delimited scope.

Borrowing does not come without a cost, however: if a function `f`
borrows a value `v` of type `T`, then the caller of the function
#emph[must] retain `v` alive until `f` has returned; the consequence is
that Rust cannot, in general, perform tail-call elimination, crucial to
the operation behaviour of many functional programs, as some resources
must be released after `f` has returned.

The reason that Rust programs depend so much on borrowing is that
unique values are the default. Linear Haskell aims to hit a different
point in the design space where regular non-linear expressions are the
norm, yet gracefully scaling up investing extra effort to enforce
linearity invariants is possible. Nevertheless, we discuss in Sec. 7.2 how
to extend Linear Haskell with borrowing.

== Linearity via monads
<sec:monads>
#cite(<launchbury_st_1995>, form: "prose") taught us a conceptually
simple approach to lifetimes: the $sans("ST")$ monad. It has a phantom
type parameter $sans(s)$ (the region) that is instantiated once at the
beginning of the computation by a $sans("runST")$ function of type:
```haskell
runST :: ∀a. (∀s. ST s a) -> a
```
This way, resources that are allocated during the
computation, such as mutable cell references, cannot escape the dynamic
scope of the call to $sans("runST")$ because they are themselves tagged
with the same phantom type parameter.

==== Region-types.
<region-types.>
With region-types such as $sans("ST")$, we cannot express typestates, but
this is sufficient to offer a safe #smallcaps[api] for freezing array or
ensuring that files are eventually closed. This simplicity (one only
needs rank-2 polymorphism) comes at a cost: we've already mentionned in
Sec. 2.2 that it forces operations to be more sequentialised than need be,
but more importantly, it does not support #emph[prima facie] the
interaction of nested regions.

#cite(<kiselyov_monadic_2008>, form: "prose") show that it is possible
to promote resources in parent regions to resources in a subregion. But
this is an explicit and monadic operation, forcing an unnatural
imperative style of programming where order of evaluation is explicit.
The HaskellR project~@boespflug_projecth_2014 uses monadic regions in the
style of Kiselyov and Shan to safely synchronise values shared between
two different garbage collectors for two different languages. Boespflug et al.
report that custom monads make writing code at an interactive
prompt difficult, compromises code reuse, forces otherwise pure
functions to be written monadically and rules out useful syntactic
facilities like view patterns.

In contrast, with linear types, values in two regions hence can safely
be mixed: elements can be moved from one data structure (or heap) to
another, linearly, with responsibility for deallocation transferred
along.

==== Idris's dependent indexed monad.
<idriss-dependent-indexed-monad.>
To go beyond simple regions, Idris~@brady_idris_2013 introduces a generic
way to add typestate on top of a monad, the $sans("ST")$ indexed monad
transformer#footnote[See #emph[e.g.]
  #link("http://docs.idris-lang.org/en/latest/st/index.html");. Where you
  will also discover that $sans("ST")$ is actually defined in terms of a
  more primitive $sans("STrans")$];. The basic idea is that everything which
must be single-threaded -- and that we would track with linearity --
become part of the state of the monad. For instance, coming back to the
sockets of Sec. 5.2, the type of $sans("bind")$ would be as follows:
```haskell
bind :: (sock :: Var) -> SocketAddress -> ST IO () [sock ::: Socket Unbound :-> Socket Bound]
```
Where $sans("sock")$ is a reference into the monads's state,
and $sans("Socket") sans("Unbound")$ is the type of $sans("sock")$
before $sans("bind")$, and $sans("Socket") sans("Bound")$, the type of
$sans("sock")$ after $sans("bind")$.

Idris uses its dependent types to associate a state to the value of its
first argument. Dependent types are put to even greater use for error
management where the state of the socket depends on whether $sans("bind")$
succeeded or not:
```haskell
-- In Idris, bind uses a type-level function (or) to handle errors
bind :: (sock :: Var) -> SocketAddress ->
  ST IO (Either () ()) [sock ::: Socket Unbound :-> (Socket Bound ‘or‘ Socket Unbound)]
-- In Linear Haskell, by contrast, the typestate is part of the return type
bind :: Socket Unbound ⊸ SocketAddress -> Either (Socket Bound) (Socket Unbound)
```
The support for dependent types in #smallcaps[ghc] is not as
comprehensive as Idris's. But it is conceivable to implement such an
indexed monad transformer in Haskell. However, this is not an easy task,
and we can anticipate that the error messages would be hard to stomach.

= Future work
<sec:future-work>
== Controlling program optimisations
<sec:controlling-optimisations>

Inlining is a cornerstone of program optimisation, exposing
opportunities for many program transformations. Yet not every function
can be inlined without negative effects on performance: inlining a
function with more than one use sites of the argument may result in
duplicating a computation. For example one should avoid the following
reduction:
$\( lambda x arrow.r x ++ x \) sans("expensive") arrow.long.r sans("expensive") ++ sans("expensive")$.

Many compilers can discover safe inlining opportunities by analysing
source code and determine how many times functions use their arguments.
(In #smallcaps[ghc] it is called the #emph[cardinality analysis]
@sergey_cardinality_2014). A limitation of such an analysis is that it
is necessarily heuristic (the problem is undecidable for Haskell).
Because inlining is crucial to efficiency, programmers find themselves
in the uncomfortable position of relying on a heuristic to obtain
efficient programs. Consequently, a small, seemingly innocuous change
can prevent a critical inlining opportunity and have rippling
catastrophic effects throughout the program. Such unpredictable
behaviour justifies the folklore that high-level languages should be
abandoned to gain precise control over program efficiency.

A remedy is to use the multiplicity annotations of $lambda_arrow.r^q$,
as cardinality declarations. Formalising and implementing the
integration of multiplicities in the cardinality analysis is left as
future work.

== Extending multiplicities
<sec:semiring-extension>
For the sake of this article, we use only multiplicities $1$ and
$omega$. But in fact $lambda_arrow.r^q$ can readily be extended to more,
following #cite(<ghica_bounded_2014>, form: "prose") and
#cite(<mcbride_rig_2016>, form: "prose");. The general setting for
$lambda_arrow.r^q$ is an ordered-semiring of multiplicities (with a join
operation for type inference). In particular, in order to support
dependent types, McBride needs a $0$ multiplicity. We may also want to
add a multiplicity for affine arguments (#emph[i.e.] arguments which
can be used at most once).

The typing rules are mostly unchanged with the caveat that
$sans("case")_pi$ must exclude $pi = 0$ (in particular we see that we
cannot substitute multiplicity variables by $0$). The variable rule
becomes: #align(center)[
  #prooftree(rule($x :_1 A lt.eq Gamma$, $Gamma tack.r x : A$))
] Where the
order on contexts is the point-wise extension of the order on
multiplicities.

In Sec. 6.3, we have considered the notion of borrowing:
delimiting life-time without restricting to linear usage. This seems to
be a useful pattern, and we believe it can be encoded as an additional
multiplicity as follows: let $beta$ be an additional multiplicity with
the following characteristics:

- $1 < beta < omega$

- $beta + beta = 1 + beta = 0 + beta = 1 + 1 = beta$

That is, $beta$ supports contraction and weakening but is smaller than
$omega$. We can then introduce a value with an explicit lifetime with
the following pattern:
```haskell
borrow :: (T ->β Unrestricted a) ->β Unrestricted a
```
The $sans("borrow")$ function makes the life-time manifest in
the structure of the program. In particular, it is clear that calls
within the argument of $sans("borrow")$ are not tail: a shortcoming of
borrowing that we mentioned in Sec. 6.3.

== Future industrial applications
<sec:future-applications>
Our own work in an industrial context triggered our efforts to add
linear types to #smallcaps[ghc];. We were originally motivated by
precisely typed protocols for complex interactions and by taming
#smallcaps[gc] latencies in distributed systems. But we have since
noticed other potential applications of linearity in a variety of other
industrial projects.

/ Streaming I/O: #block[
    Program inputs and outputs are frequently much larger than the available
    #smallcaps[ram] on any single node. Rather than building complex
    pipelines with brittle explicit loops copying data piecemeal to spare
    our precious #smallcaps[ram];, one approach is to compose combinators
    that transform, split and merge data wholemeal but in a streaming
    fashion. These combinators manipulate
    #emph[first-class streams] and guarantee bounded memory usage, as
    in the below infinitely running echo service:
    ```haskell
    receive :: Socket -> IOStream Msg
    send :: Socket -> IOStream Msg -> IO ()
    echo isock osock = send osock (receive isock)
    ```
    However, reifying sequences of IO actions (socket reads) in this way
    runs the risk that effects might be duplicated inadvertently. In the
    above example, we wouldn't want to inadvertently hand over the receive
    stream to multiple consumers, or the abstraction of wholemeal I/O
    programming would be broken (like in
    #cite(<lippmeier_polarized_2016>, form: "prose");, Section 2.2), because
    neither consumer would ultimately see the same values from the stream.
    If say one consumer reads in the stream first, the second consumer would
    see an empty stream --- not what the first consumer saw. We have seen
    this very error several times in industrial projects, where the symptoms
    are bugs whose root cause are painful to track down. A linear type
    discipline would prevent such bugs.

  ]
/ Programming foreign heaps: #block[
    Complex projects with large teams invariably involve a mix of
    programming languages. Reusing legacy code is often much cheaper than
    reimplementing it. A key to successful interoperation between languages
    is performance. If all code lives in the same address space, then data
    need not be copied as it flows from function to function implemented in
    multiple programming languages. Trouble is, language A needs to tell
    language B what objects in language A's heap still have live references
    in the call stack of language B to avoid too eager garbage collection.

    For instance, users of `inline-java` call the #smallcaps[jvm] from
    Haskell via the #smallcaps[jni];. The #smallcaps[jvm] implicitly creates
    so-called #emph[local references] any time we request a Java object from
    the #smallcaps[jvm];. The references count as #smallcaps[gc] roots that
    prevent eager garbage collection. For performance, local references
    have a restricted scope: they are purely thread-local and never survive
    the call frame in which they were created. Both restrictions to their
    use can be enforced with linear types.

  ]
/ Remote direct memory access: #block[
    Section 5.1 is an example of an #smallcaps[api] requiring
    #emph[destination-passing style];. This style often appears in
    performance-sensitive contexts. One notable example from our industrial
    experience is #smallcaps[rdma] (Remote Direct Memory Access), which
    enables machines in high-performance clusters to copy data from the
    address space in one process to that of a remote process directly,
    bypassing the kernel and even the #smallcaps[cpu];, thereby avoiding any
    unneeded copy in the process.

    One could treat a remote memory location as a low-level resource, to be
    accessed using an imperative #smallcaps[api];. Using linear types, one
    can instead treat it as a high-level value which can be written to
    directly (but exactly once). Using linear types the compiler can ensure
    that, as soon as the writing operation is complete, the destination
    computer is notified.

  ]

= Conclusion
<sec:conclusion>
This article demonstrates how an existing lazy language, such as
Haskell, can be extended with linear types, without compromising the
language, in the sense that:

- existing programs are valid in the extended language without
  modification,

- such programs retain the same operational semantics, and in particular

- the performance of existing programs is not affected,

- yet existing library functions can be reused to serve the objectives
  of resource-sensitive programs with simple changes to their types, and
  no code duplication.

In other words: regular Haskell comes first. Additionally, first-order
linearly typed functions and data structures are usable directly from
regular Haskell code. In such a setting their semantics is that of the
same code with linearity erased.

Linear Haskell was engineered as an unintrusive design, making it
tractable to integrate to an existing, mature compiler with a large
ecosystem. We have developed a prototype implementation extending
#smallcaps[ghc] with multiplicities. As we hoped, this design integrates
well in #smallcaps[ghc];.

Even though we change only #smallcaps[ghc];'s type system, we found that
the compiler and runtime already had the features necessary for unboxed,
off-heap, and in-place data structures. That is, #smallcaps[ghc] has the
low-level compiler primitives and #smallcaps[ffi] support to implement,
for example, mutable arrays, mutable cursors into serialised data, or
off-heap foreign data structures without garbage collection. These
features could be used before this work, but their correct use put some
burden-of-proof on the programmers. Linearity unlocks these
capabilities for safe, compiler-checked use, within pure code.

#block[
  == Acknowledgments
  This work has received funding from the European Commission through the #smallcaps[sage]
  project (Grant agreement no. 671500 (#link("http://www.sagestorage.eu"))), as well as from Swedish Research Council via the establishment of
  the Centre for Linguistic Theory and Studies in Probability
  (#smallcaps[clasp];) at the University of Gothenburg. We thank Manuel
  Chakravarty, Stephen Dolan and Peter Thiemann for their valuable
  feedback on early versions of this paper.
]

#bibliography("references.bib")
