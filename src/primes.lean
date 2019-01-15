import data.nat.prime
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 We will use basic definitions about primes and divisibility taken from the mathlib
 library.  The home page of the library is
 <a href="https://github.com/leanprover/mathlib">https://github.com/leanprover/mathlib</a>
 and you can browse and search the source code there.  If you set things up in a standard
 way, you should have a copy of the library in more or less the same place as your own
 Lean files, with directory structure like this:
 <ul>
  <li><span class="path">.git</span>: a director that we can ignore. </li>
  <li><span class="path">.gitignore</span>,
      <span class="path">leanpkg.path</span>,
      <span class="path">leanpkg.toml</span>: files that we can ignore</li>
  <li>_target
   <ul>
    <li>deps
     <ul>
      <li>mathlib
       <ul>
        <li>Subdirectories algebra, analysis, category, computability, data, ....
         These contain uncompiled, human-readable files with extension .lean,
	 and also compiled files with extension .olean.
        </li>
       </ul>
      </li>
     </ul> 
    </li>
   </ul>
  </li>
  <li>src
   <ul>
    <li>Your own Lean files, such as the one shown here.</li>
   </ul>
  </li>
 </ul>
 <br/><br/>
 The line `import data.nat.prime` allows us to use definitions
 and results from the file <span class="mathlib">data/nat/prime.lean</span>.  For
 example, that file proves that $2$ is prime, and gives the name
 `prime_two` to that fact.  (However, see the comment on the next line.)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
open nat
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  The file <span class="mathlib">data/nat/prime.lean</span> proves
  a nnumber of facts.  For example, it proves that $2$
  is prime, and gives the name `prime_two` to that fact.
  However, the same file also says `namespace nat` near the top.
  Because of this, the full name of the relevant theorem is really
  `nat.prime_two`.  The line `open nat`
  in the current file allows us to drop the `nat` prefix.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

lemma larger_prime : ∀ n : ℕ, ∃ p, (prime p) ∧ (p > n) := 
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  This line states the result that we want to prove, and attaches the name
  `larger_prime` to the result.
  <ul>
    <li>There are various symbols that do not appear on your keyboard.  These
    can usually be entered in Visual Studio Code using LaTeX syntax.  For example,
    you can type `\forall` followed by a space, and the
    `\forall` will automatically turn into into
    `∀`.  For
    `ℕ`, `ℤ`,
    `ℚ` and `ℝ` one can enter
    `\nat`, `\int`,
    `\rat` and `\real`.
   </li>
   <li>To indicate that $n$ is in $ℕ$ we write `n : ℕ`
    rather than `n ∈ ℕ`, following the conventions of type
    theory rather than set theory.
   </li>
   <li>The expression `prime p` refers to the definition of primality
    taken from the file <span class="mathlib">data/nat/prime.lean</span>.
    That definition essentially gives a function from natural numbers to
    truth values.  To apply that function to the argument $p$, we write `prime p`
    (following the conventions of Lisp-like programming languages) rather than
    `prime(p)` as in traditional functional notation.
    Note that if we had not had the line `open nat`, we
    would have had to say `nat.prime p` instead of
    `prime p`.
   </li>
   <li>Note the commas associated with the quantifiers, and the
    `:=` at the end of the line.  If you have this file
    open in Visual Studio Code, and you take out the first comma, then you should
    see three error messages in the Lean messages window.  (If you do not see the
    relevant window, you should press CTRL-SHIFT-ENTER, or click the
    <img src="../../images/left_msg_icon.png"/> icon near the top of the screen.)
    None of those error messages is optimal, but
    <span class="error">unknown identifier 'n'</span> gives some indication of
    the location of the problem.  On the other hand, if you leave out the
    <span class="error">:=</span> then the error messages are completely opaque.
   </li>
  </ul>
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
begin
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  This marks the beginning of the proof.  For some simple kinds of proofs
  it is not necessary to have a `begin ... end` wrapper.  For some
  complicated proofs there will be nested `begin ... end` blocks to
  prove various intermediate claims that arise in the course of the proof.
  <br/><br/>
  Inside the `begin ... end` block, we enter
  "tactic mode", as discussed in Chapter 5 of the book
  <a href="https://leanprover.github.io/theorem_proving_in_lean/">Theorem
  Proving in Lean</a>.  (References to "Chapter n" or "Section p.q" below
  will always refer to this book.)  This can be explained as follows.  A
  Lean proof is a kind of complex data structure.  Outside of tactic mode,
  we can construct a proof by programming methods, in which we explicitly
  apply various functions to simpler structures that we have already defined.
  Inside tactic mode, we can construct proofs by a kind of dialogue with
  the proof assistant, which is much more similar to a traditional
  writer's imagined dialogue with the reader.
  <br/><br/>
  If you have this file open in Visual Studio Code, and you click at the
  end of the word `begin`, you should see a message like this in the
  Lean messages window:
  <div class="lean_messages">
   ⊢ ∀ (n : ℕ), ∃ (p : ℕ), prime p ∧ p > n
  </div>
  This states our current proof goal.  (If you do not see the relevant
  window, you should press CTRL-SHIFT-ENTER, or click the
  <img src="../../images/left_msg_icon.png"/> icon near the top of the
  screen.)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 intro n,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  We are aiming to prove a statement that is universally quantified over the
  natural numbers.  In traditional writing, we would start by saying "let $n$
  be an arbitrary natural number", or some similar phrase.  The line
  `intro n,` plays a similar role in Lean.
  <br/><br/>
  If you click on the end of this line in VS Code, you will see that the tactic
  state has changed to 
  <div class="lean_messages">
    n : ℕ
    ⊢ ∃ (p : ℕ), prime p ∧ p > n
  </div>
  This means, essentially, that we are working in a context where we have a given
  natural number $n$, and we aim to prove that there is a prime $p$ with $p>n$.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 let m := fact n + 1,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  We now define $m$ to be $n!+1$.  Again note the terminating comma.  The tactic
  state changes to
  <div class="lean_messages">
   n : ℕ,
   m : ℕ := fact n + 1
   ⊢ ∃ (p : ℕ), prime p ∧ p > n
  </div>
  incorporating the definition of $m$ in the context.
  <br/><br/>
  In VS Code you can hover over the word `fact` with
  your mouse to see that the full name is `nat.fact`
  and that the type is `ℕ → ℕ`, and there is also a
  comment explaining that `fact` is the factorial
  function.  If you hold the CTRL key while hovering, you will see the actual
  recursive definition of the function.  If you hold the CTRL key and click,
  then you will jump to the file where that definition appears.  Alternatively,
  you can right-click and then type F12 or Alt-F12.
  For this particular definition, the relevant file is 
  <span class="mathlib">data/nat/basic.lean</span>.  Note that we did not
  explicitly import `data.nat.basic`, but we
  imported `data.nat.prime`, which imports
  `data.nat.sqrt`, which imports
  `data.nat.basic`.  Some standard properties of
  factorials are proved in the same place.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 let p := min_fac m,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 This line defines $p$ using the function `min_fac`
 defined in <span class="mathlib">data/nat/basic.lean</span>.  This is
 supposed to be defined by the requirement that
 `min_fac k` is the smallest $d>1$ such that $d$
 divides $k$.  This makes sense for $k=0$ (with
 `min_fac 0 = 2`) and for $k>1$, but this
 characterisation would leave `min_fac 1` undefined.
 The approach taken by the Lean library is to arbitrarily define 
 `min_fac 1 = 1`.  This of course means that some
 theorems about the properties of `min_fac` will
 need auxiliary hypotheses.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 have m_gt_1 : m > 1, {apply nat.succ_lt_succ,apply fact_pos},
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 We now want to show that $m>1$.  We use the keyword
 `have` to state this fact, and introduce the name
 `m_gt_1` for it.  (It is possible to reorganise
 the proof to avoid introducing names for minor intermediate facts like this,
 and many experts seem to prefer that style.  However, we feel that such
 names make it much easier for the neophyte to understand what is happening.)
 The proof of `m_gt_1` involves two ingredients:
 <ul>
  <li>The fact that $n!>0$, which is proved in
   <span class="mathlib">data/nat/basic.lean</span> under the name
   `fact_pos`.
  </li>
  <li>The fact that $a>b$ implies $a+1>b+1$.  This does not come from mathlib,
   but from the core Lean library.  The relevant file is
   <span class="library">init/data/nat/lemmas.lean</span> under the
   <span class="path">lib/lean/library/</span> directory of the Lean
   installation, which may well be a system directory rather than a user
   directory.  The name of this fact is `succ_lt_succ`.  (Here `lt` stands
   for "less than", and `succ` refers to the successor operation
   $a\mapsto a+1$.  As in Peano arithmetic, addition is actually defined in
   terms of the successor operation rather than the other way around.)
  </li>
  In VS Code, it is illuminating to click in various places in the above
  line and examine how the goal state changes as we state the claim that
  $m>1$, use `succ_lt_succ` to reduce to the claim that $n!>0$, and then
  appeal to `fact_pos` to prove the reduced claim.  Note also that the
  keyword  `apply` refers to a "tactic", which manipulates the goal
  state.  Proof tactics in general are described in
  <span class="tpil">Chapter 5</span>.  One can hover over the word
  `apply` to see some information about how this tactic works.
 </ul>
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 have m_ne_1 : m ≠ 1 := ne_of_gt m_gt_1,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 We now deduce that $m\neq 1$.  This uses the result named `ne_of_gt`,
 which says that $a>b\Rightarrow a\neq b$.  Systems like Lean are set
 up so that a proof of $P\Rightarrow Q$ is essentially the same thing
 as a function from proofs of $P$ to proofs of $Q$.  Here `m_gt_1` is
 a proof that $m>1$, and we are applying `ne_of_gt` to it to get a
 proof that $m\neq 1$.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 have p_gt_0 : p > 0, {apply min_fac_pos},
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 We now state that $p>0$, attach the name `p_gt_0` to this claim, and
 prove it by applying the theorem named `min_fac_pos` from
 <span class="mathlib">data/nat/prime.lean</span>.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 have p_prime : prime p := min_fac_prime m_ne_1,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 We now state that $p$ is prime, attach the name `p_prime`
 to this claim, and prove it by applying the theorem named
 `min_fac_prime` from
 <span class="mathlib">data/nat/prime.lean</span>.
 <br/><br/>
 Recall that `min_fac n` was arbitrarily defined to be
 $1$ when $n=1$, so the theorem that `min_fac n` is prime
 is only valid with the side condition that $n\neq 1$.  The theorem
 `min_fac_prime` is essentially a function that takes
 as input a natural number $n$ together with a proof that $n\neq 1$, and produces
 a proof that `min_fac n` is prime.  However, things are
 set up in such a way that a proof of $n\neq 1$ contains the value of $n$ as part
 of the data, so we do not need to supply $n$ explicitly.  This kind of thing
 is handled by Lean's framework of implicit arguments.  The declaration of
 `min_fac_prime` has the shape
 <div class="code">
  theorem min_fac_prime {n : ℕ} (n1 : n ≠ 1) : prime (min_fac n) := ...
 </div>
 with the curly brackets around `{n : ℕ}` indicating that
 $n$ will be determined from the context.  (If for some reason we want to supply
 $n$ explicitly, we can use the notation `@min_fac_prime`
 instead of `min_fac_prime`.)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 have not_p_le_n : ¬ p ≤ n, {
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 We now state and prove the negation of $p\leq n$.  It is part of the basic logical
 framework of Lean that a proof of this negation is the same as a procedure that
 takes a hypothetical proof of $p\leq n$ and produces a contradiction.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
  intro p_le_n,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 This line means: "let `p_le_n` be a hypothetical proof
 that $p\leq n$".  Given such a hypothetical proof, we need to produce a contradiction.  
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
  have d0 : p ∣ fact n := dvd_fact p_gt_0 p_le_n,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  We now prove that $p$ divides $n!$.  The proof appeals to the fact (named
  `dvd_fact`) that $a$ divides
  $b!$ whenever $a>0$ and $a\leq b$.  We supply the explicit arguments
  `p_gt_0` and `p_le_n` to
  verify the hypotheses; the implicit arguments $p$ and $n$ are deduced from
  the context. 
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
  have d1 : p ∣ fact n + 1 := min_fac_dvd m,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 We now claim that $p$ divides $m=n! + 1$.  As $p$ was defined to be
 `min_fac m`, this amounts to the claim that the
 `min_fac` function was correctly defined.  This was proved in
 `prime.lean` under the name
 `min_fac_dvd`.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
  have d  : p ∣ 1 := (nat.dvd_add_iff_right d0).mpr d1,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 We now want to prove that $p$ divides $1$.  For this we appeal to the fact that
 if $a$ divides $b$, then $a$ divides $c$ iff $a$ divides $b+c$.  This fact has
 the name `dvd_add_iff_right`.  Unfortunately, there are
 two versions of this fact that are currently visible.  One of them comes from
 the file <span class="library">init/algebra/ring.lean</span>, and applies
 to an arbitrary commutative ring.  The other comes from
 <span class="library">init/data/nat/lemmas.lean</span>, and
 applies only to `ℕ` (which is a semiring rather than a ring).
 Note that both of these are in the core Lean library, not in mathlib.  We need to
 use the version for `ℕ`, so we need to resolve the
 ambiguity by providing the explicit prefix in
 `nat.dvd_add_iff_right`.
 <br/><br/>
 By applying `nat.dvd_add_iff_right` to
 `d0`, we obtain a proof that $p$ divides $n!+1$ iff $p$
 divides $1$.  The syntax `(...).mpr` extracts the
 right-to-left half of this equivalence, which we can then apply to the fact
 `d1` to obtain a proof that $p$ divides $1$.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
  exact prime.not_dvd_one p_prime d
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 Our goal is to produce a contradiction, or equivalently to prove the proposition
 `false`.  We do this using the keyword
 `exact` (which is the name of a kind of tautological tactic)
 followed by an expression that evaluates to `false`.  The
 theorem `prime.not_dvd_one` says that no prime divides $1$.
 Equivalently, it is a function that accepts a proof that a number is prime, together
 with a proof that that number divides $1$, and produces
 `false`.  We can thus apply
 `prime.not_dvd_one` to the ingredients
 `p_prime` and `d` to obtain the
 required contradiction.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 },
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 have p_gt_n : p > n := lt_of_not_ge not_p_le_n,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 We now use the result `lt_of_not_ge` to convert our proof
 of `¬ p ≤ n` to a proof of $p > n$.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 existsi p,split,exact p_prime,exact p_gt_n
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 We are now ready to wrap up.  The proof goal is to prove that there exists a number
 with certain properties.  We use the `existsi` tactic to
 introduce the number that we claim has the relevant properties.  This changes the
 proof goal: we now need to prove that $p$ is prime and $p>n$.  These two claims are
 initially combined as the single goal `(prime p) ∧ (p > n)`.
 We use the `split` tactic to divide this into two goals
 `prime p` and `p > n`.  We have
 already proved these two facts under the names `p_prime`
 and `p_gt_n`, so we can just use the
 `exact` tactic twice to complete the proof.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
end
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

#check larger_prime
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Lean accepts correct proofs without explicit acknowledgement.  To
get more positive feedback, we can enter
`#check larger_prime`: this will restate
the fact that we have proved in the message window.

~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

