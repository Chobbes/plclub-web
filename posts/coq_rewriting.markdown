## `R E S P E C T` : Find Out What It Means To The Coq Standard Library

### Lucas Silver
#### PL Club at the University of Pennsylvania

This blog post is a companion to the following [code](https://github.com/lag47/Rewrite-Tutorial). Please follow along with that file.

Prerequisites:
(Calvin: Got rid of the first bullet point here. It seemed condescending to me. Anybody who will ever read this will have a basic math background)
* Basic Coq Knowledge: at least through `Relations.v` from [Software Foundations](https://softwarefoundations.cis.upenn.edu/lf-current/toc.html)
* Basic Type Class Knowledge: background from any language should be fine


In informal mathematics rewriting is so ubiquitous that it is often not taught explicity. We do it all the time without bothering to justify it. However, in a formal logical system like Coq, every rewrite must be justified. In order to justify something, we must first understand what it is (Calvin: not sure that I like this transition---are we "understanding what rewrites are", or something else?). 

(Calvin: I feel like this should start much less generally by introducing the problem in the context of `=`)
Suppose, we have some relation `R : A -> A -> Prop` and two values `x y : A` such that `R x y`. We have some context `K`. Our goal is `K[x]` and we would prefer our goal to be `K[y]`. To do this we want to rewrite `x` into `y` under `K`. In order for this to be justified, we need to know that as long as we know `R x y`, we also know that `K[y]` implies `K[x]`. To introduce some other vocabularly, to say `R` is proper with respect to `K` is the same as the previous sentence.

The `=` relation in Coq is strong enough that it is proper under any relation. This means that, if we know `x = y`, then for any ontext `K`, we can transform a goal of `K[x]` into one of `K[y]`


These notions (Calvin: what notions? I know you mean proper / respectful, but I'm not sure that would be clear to a reader, and from what's written it's not clear that "proper" and "respects" are separate things?) are implemented as type classes in the Coq standard library. We will go over the exact instances we will need to provide later. For now, just keep in mind that Coq has provided a series of tactics that, given certain type class instances, will automatically figure out the justifications for rewrites.

(Calvin: this transition is really awkward. Maybe a forward pointer to rewrite when talking about "a series of tactics" earlier. I also feel like we're saying "justification" a lot)
Luckily, the Coq's `rewrite` tactic can make providing this justification easier. 

(Calvin I almost feel like this post should start with an example like this. "Here's rewriting with equality. Wow that's useful. Wouldn't it be great if we could rewrite things under different relations?" Currently I don't feel like the motivation is there at the beginning.)
So let us go through some concrete examples showing the strength of rewriting. Consider the following proposition and proof script

```coq
Goal forall (a b c d : Z), a = b -> b = c -> c = d -> a = d.
Proof.
  intros a b c d Hab Hbc Hcd. rewrite Hab. rewrite Hbc. auto.
Qed.
```

That is essentially just the transitivity property of equality extendend to 4 elements. Note how we prove this using two rewrites instead of two applications of the transitivity property. (Calvin: I guess as a reader at this point I'm kind of like "so what? Who would do this by transitive property anyway?" Especially since I would prove the transitive property using rewrites anyway? I wonder if it's better to go straight into the second example?)

Now let's look at a slightly more complicated example. The following proposition is trivially simple if we are given the ability to rewrite.

```coq
Goal forall (a b c x y z : Z), a = x -> b = y -> c = z -> 
                                           a + b + c = x + y + z.
Proof.
  intros a b c x y z Hax Hby Hcz. rewrite Hax. rewrite Hby. rewrite Hcz.
  reflexivity.
Qed.
```

Unlike the previous example, it is not immediately obvious how we would prove this proposition without rewriting. In this case we are rewriting integers under the context of addition. (Calvin: this is good, I think we should really emphasize what the context is in the different examples)

Now that we've seen what we can do with rewriting in its most flexible and powerful form, let's see how we can recover that for other relations.

Suppose we have an integer `k` and consider modular arithmetic modulo `k`. So our relation will be `x ≡ y` means that `x` is equivalent to `y` mod `k`. The definition given in the file is equivalent to a division based definition and comes for [Bezout coefficients](https://en.wikipedia.org/wiki/B%C3%A9zout%27s_identity). However, this is not really important for our purposes. `≡` is the notation we will be using for the relation, defined in the file as `equiv`.

We can start by showing the `≡` is an equivalence relation and registering that fact as a type class.

```coq
Instance equiv_equiv : Equivalence equiv.
Proof.
  ...
Qed.
```

The proof is unrelated to the subject of this post, so it has been left out. Now we can try something similar to our first example. Once again we will be able to complete the proof only using rewrites, without needing to specifically apply any lemmas or needing to know anything about the structure of our relation.

```coq
Goal forall (a b c d : Z), a ≡ b -> b ≡ c -> c ≡ d -> a ≡ d.
Proof.
  intros a b c d Hab Hcb Hcd. rewrite Hab. rewrite Hcb. auto.
Qed.
```

(Calvin: as a reader I feel confused by this paragraph. "I thought we were talking about proper!" And it's not clear that transitivity is enabling the `rewrite` tactic to work here. This reads a bit confusingly because now I'm like "wait, symmetry? Reflexivity? What?" I do think bringing this up is very good, though! I just think that we should maybe structure this a bit differently. I think to the average beginner Coq programmer it's not obvious that these typeclasses affect tactics like symmetry and reflexivity and rewrite, so I think it's actually great to start with that?)
In fact, all we needed to do the above rewrites was the transitivity of `≡`. You can rearrange the companion file and see this for yourself. However, the fact that it is an equivalence relation gives us some extra useful tactics. If we want to flip the relation in either a goal or a hypothesis, we can use the `symmetry` tactic, and we can use `reflexivity` to prove that too expressions that are syntactically equal are related by `≡`.

Now let us proceed to a more complicated example. We can start by observing and proving that `k ≡ 0`.

```coq
Lemma k_equiv_0 : k ≡ 0.
Proof.
  ...
Qed.
```

Now let's try to prove some basic propositions by rewriting `k` into `0`. But, what happens with the following proof script in the companion code?

```coq
Goal forall x, x + k ≡ x.
Proof.
  intros. Fail rewrite k_equiv_0. 
Abort.
```

It didn't work! The terrifying error message you should have seen is just related to type class resolution in Coq and is not obviously helpful. (Calvin: or perhaps obviously not helpful, ha)

So, without useful error messages to guide us, let's try to figure out what is wrong. Recall what I wrote earlier about rewriting under different contexts. We need to prove that addition is proper with respect to `≡` (Calvin: I think it's still a little unclear what "proper" means at this point, so I'm not sure if this is clarifying enough. Also I think this should maybe be where we introduce rewriting under different contexts? Not sure.). It makes sense that we should need to prove this, because we can easily construct functions that are not proper. For instance, consider 

```coq
Definition f x y := 
  if x ?= 0 && y ?= 0 
  then 0
  else 1.
```
which clearly distinguishes between `0` and `k` in general. (Calvin: maybe have a specific example of how this distinguishes between 0 and k)

In the scary error message you may have noticed the term `Proper` and the notation `==>`. So we can start our search there.

```coq
Definition Proper {A : Type} (R : A -> A -> Prop) : A -> Prop := 
  fun a => R a a
```

(Calvin: "We provide some more basic examples in the We haven't gotten very far with this function."?)
(Calvin: I feel like calling it a definition would be a little nicer than calling it a function, because you don't really compute with it? Maybe that's just me.)
So it is the function that takes a relation `R`, a single element `a` and uses `a` for both of `R`'s inputs. We provide some more basic examples in the  We haven't gotten very fair with this function. Now note that `==>` is notation for the function `respectful`. 

```coq 
Definition respectful {A B : Type} (R : A -> A -> Prop)
  (R' : B -> B -> Prop) : (A -> B) -> (A -> B) -> Prop :=
    fun f g => forall x y, R x y -> R' (f x) (g y)
```

This is a more interesting looking definition, `respectful` takes a relation over inputs (`R`) and a relation over outputs (`R'`), and creates a relation over functions. In fact if we apply `respectful` to the same `f` twice, we get the proposition
```coq
forall x y, R x y -> R' (f x) (f y)
```

(Calvin: Hmmm. Maybe we should call it `K` instead of `f` or something to better link it to the informal definitions earlier?)
This should start to look like the informal definitions from the beginning of this post. Consider the following proposition

(Calvin: we kind of don't directly relate ≡ and equiv, so people might not realize that ≡ is notation for equiv right away)
```coq
Goal Proper (equiv ==> equiv) (fun x => x + 2).
Proof.
    intros ? ? ?.
    ...
Qed. 
```
(Calvin: I feel like I want to see these definitions actually unfolded in the blog post. I know it shows up after intros ? ? ? in the file, but I think it's pretty important to understand how proper and respectful fit together... (equiv ==> equiv) (fun x => x + 2) (fun x => x + 2) which then turns into... forall x y, x ≡ y -> x + 2 ≡ y + 2)
Intuitively, this proposition says that given any `x` and `y` such that `x ≡ y`, then `x + 2 ≡ y + 2`. For a general rule consider the following proposition

```coq
  Proper (R1 ==> R2 ==> ... ==> Rn ==> Rm) f
```

It means that given two sequences of variables `x1 ... xn` and `y1 .. yn` such that given any `i`, `Ri xi yi`,
```coq 
 Rm (f x1 .. xn) (f y1 .. yn) 
```
So all of the relations to the left of a `==>` relate arguments and the rightmost relation relates the outputs.

(Calvin: might be nice to provide a bit of context here... "Returning to our modular arithmetic example, recall that we were having trouble rewriting under addition. We can use Proper and respectful to...")
(Calvin: Side note. At this point the relationship between proper / respectful and rewrite has only been implied. It might be nice to say explicitly somewhere "rewrite looks for proper / respectful instances to rewrite under contexts" or something better than that.)
Now we can return to our modular arithmetic example. First let us prove that addition respects `≡` in its second argument.

```coq
Instance add_proper_r {x: Z} : Proper (equiv ==> equiv) (Z.add x).
Proof.
  ...
Qed.
```

Now we can rewrite in the second argument of addition:

```coq
Goal forall x, x + k ≡ x.
Proof.
  intros. rewrite k_equiv_0.
  rewrite Z.add_comm. simpl. reflexivity.
Qed.
```

Note that we still can't rewrite in the left argument.

```coq
Goal forall x, k + x ≡ x.
Proof.
  intros. 
  Fail rewrite k_equiv_0. 
Abort.  
```

In order to rewrite in the left argument, we need to show that addition is proper in all of its arguments. This proof is made simple by our existing proper instance and the fact that addition is commutative.

```coq
Instance add_proper : Proper (equiv ==> equiv ==> equiv) Z.add.
Proof.
  intros x y  Hxy z w Hzw.
  rewrite <- Hzw. Fail rewrite Hxy. 
  rewrite Z.add_comm. rewrite Hxy. rewrite Z.add_comm.
  reflexivity.
Qed.
```

Now we can stress test our rewriting with the following example.
```coq
 Goal forall x : Z, 
  k + (x + ( k + k ) + k) ≡ 
  k + k + (k + k) + ( (k + k) + (k + k)  ) + x. 
  Proof.
    intros. rewrite k_equiv_0. simpl. rewrite Z.add_comm. simpl.
    rewrite Z.add_comm. reflexivity.
  Qed.
```

Note that there is only one `x` on each side of the equivalence, so once we replace all `k`'s with `0`, the proof is vastly simpler.

To wrap up, let's look at another example where rewriting is incredibly useful. Suppose we want to model stateful computations in Coq.

```coq
Definition State (A : Type) := S -> (S * A).
```
A stateful computation is a function that when given an initial state of type `S`, produces an output state as well as a result of type `A`. We can give this type a monadic structure with the following functions

```coq
Definition ret {A} (a : A) := fun s : S => (s,a).

Definition bind {A B} (m : State A) (f : A -> State B) :=
  fun s => let '(s',a) := m s in f a s'.
```

`ret` captures the notion of a pure computation returning `a`, and therefore leaves its input state alone.

`bind` captures the notion of concatenating two stateful computations by running the first one and threading the output state as input to the next one. It actually generalizes that notion a bit, taking as its argument a function `f : A -> State B`, which can be views as a family of stateful computations indexed over `A`. As is custumary, we denote `bind` with the infix operator `>>=`

We create a notion of stateful computation equivalence as follows:

```coq
Definition state_eq {A : Type} (m1 m2 : State A) :=
  forall (s : S), m1 s = m2 s.
```

I.e., two stateful computations are equivalent if they evaluate to the
same output state and value for every input state. We denote this
equivalence with `≈`, and provide an instance of the `Equivalence`
type class.

As `State` is a monad, we are able to prove the monad laws up to state equivalence:

```coq
Lemma bind_ret : forall (A B : Type) (a : A) (f : A -> State B),
    ret a >>= f ≈ f a.
Proof.
  ...
Qed.

Lemma ret_bind : forall (A : Type) (m : State A),
    m >>= ret ≈ m.
Proof.
  ...
Qed.

Lemma bind_bind : forall (A B C : Type) (m : State A) 
                          (f : A -> State B) (g : B -> State C),
    (m >>= f) >>= g ≈ (m >>= (fun a => f a >>= g)).
Proof.
  ...
Qed.
```

Now suppose we want to rewrite these equations. This would be a nice thing to have because these equations require no knowledge of the definitions of `ret` and `bind`.

First, we can lift our equivalence over `State B` to an equivalence  over `A -> State B` using the `pointwise_relation` function.

(Calvin: name? pointwise_relation?)
```coq
Definition {A B : Type} (R : B -> B -> Prop) : 
  (A -> B) -> (A -> B) -> Prop :=
  fun f g => forall a, R (f a) (g a)
```
This captures the notion that given equal inputs, `f` and `g` produce related outputs.

Now we want to show that `bind` respects the stateful equivalence relation given arguments that are similarly equivalent. 

```coq
Instance proper_monad {A B: Type} : Proper 
  (@state_eq A ==> pointwise_relation A state_eq ==> @state_eq B) 
    (bind).
Proof.
  ...
Qed.
```

Now we can rewrite using the monad laws under bind. Consider the following example.
```coq
Goal forall (A B :Type) (a : A) (f : A -> State B),
    ret a >>= (fun a' => f a') >>= ret ≈ f a.
Proof.
  intros. rewrite bind_bind. rewrite bind_ret. rewrite ret_bind.
  reflexivity.
Qed.
```

Hopefully, you found this to be a useful introduction to rewriting in Coq. There is much more to learn, but you should have a strong enough foundation to learn it on your own. Good luck proving things!
