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
 The line <span class="code">import data.nat.prime</span> allows us to use definitions
 and results from the file <span class="path">mathlib/data/nat/prime.lean</span>.  For
 example, that file proves that $2$ is prime, and gives the name
 <span class="code">prime_two</span> to that fact.  (However, see the comment on the next line.)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
open nat
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  The file <span class="path">mathlib/data/nat/prime.lean</span> proves that $2$
  is prime, and gives the name <span class="code">prime_two</span> to that fact.
  However, the same file also says <span class="code">namespace nat</span> near the top.
  Because of this, the full name of the relevant theorem is really
  <span class="code">nat.prime_two</span>.  The line <span class="code">open nat</span>
  in the current file allows us to drop the <span class="code">nat</span> prefix.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

lemma larger_prime : ∀ n : ℕ, ∃ p, (prime p) ∧ (p > n) := 
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  This line states the result that we want to prove, and attaches the name
  <span class="code">larger_prime</span> to the result.
  <ul>
    <li>There are various symbols that do not appear on your keyboard.  These
    can usually be entered in Visual Studio Code using LaTeX syntax.  For example,
    you can type <span class="code">\forall</span> followed by a space, and the
    <span class="code">\forall</span> will automatically turn into into
    <span class="code">∀</span>.  For
    <span class="code">ℕ</span>, <span class="code">ℤ</span>,
    <span class="code">ℚ</span> and <span class="code">ℝ</span> one can enter
    <span class="code">\nat</span>, <span class="code">\int</span>,
    <span class="code">\rat</span> and <span class="code">\real</span>.
   </li>
   <li>To indicate that $n$ is in $ℕ$ we write <span class="code">n : ℕ</span>
    rather than <span class="code">n ∈ ℕ</span>, following the conventions of type
    theory rather than set theory.
   </li>
   <li>The expression <span class="code">prime p</span> refers to the definition
    of primality taken from the file
    <span class="path">mathlib/data/nat/prime.lean</span>.  That definition
    essentially gives a function from natural numbers to truth values.  To apply
    that function to the argument $p$, we write <span class="code">prime p</span>
    (following the conventions of Lisp-like programming languages) rather than
    <span class="code">prime(p)</span> as in traditional functional notation.
    Note that if we had not had the line <span class="code">open nat</span>, we
    would have had to say <span class="code">nat.prime p</span> instead of
    <span class="code">prime p</span>.
   </li>
   <li>Note the commas associated with the quantifiers, and the
    <span class="code">:=</span> at the end of the line.  If you have this file
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
  it is not necessary to have a <span class="code">begin ... end</span> wrapper.
  For some complicated proofs there will be nested
  <span class="code">begin ... end</span> blocks to prove various intermediate
  claims that arise in the course of the proof.
  <br/><br/>
  Inside the <span class="code">begin ... end</span> block, we enter
  "tactic mode", as discussed in Chapter 5 of the book
  <a href="https://leanprover.github.io/theorem_proving_in_lean/">Theorem
  Proving in Lean</a>.  This can be explained as follows.  A Lean proof is a
  kind of complex data structure.  Outside of tactic mode, we can construct a
  proof by programming methods, in which we explicitly apply various functions
  to simpler structures that we have already defined.  Inside tactic mode, we
  can construct proofs by a kind of dialogue with the proof assistant, which
  is much more similar to a traditional writer's imagined dialogue with the reader.
  <br/><br/>
  If you have this file open in Visual Studio Code, and you click at the end
  of the word <span class="code">begin</span>, you should see a message like
  this in the Lean messages window:
  <div class="lean_messages">
   ⊢ ∀ (n : ℕ), ∃ (p : ℕ), prime p ∧ p > n
  </div>
  This states our current proof goal.  (If you do not see the relevant window,
  you should press CTRL-SHIFT-ENTER, or click the
  <img src="../../images/left_msg_icon.png"/> icon near the top of the screen.)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 intro n,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  We are aiming to prove a statement that is universally quantified over the
  natural numbers.  In traditional writing, we would start by saying "let $n$
  be an arbitrary natural number", or some similar phrase.  The line
  <span class="code">intro n,</span> plays a similar role in Lean.
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
  In VS Code you can hover over the word <span class="code">fact</span> with
  your mouse to see that the full name is <span class="code">nat.fact</span>
  and that the type is <span class="code">ℕ → ℕ</span>, and there is also a
  comment explaining that <span class="code">fact</span> is the factorial
  function.  If you hold the CTRL key while hovering, you will see the actual
  recursive definition of the function.  If you hold the CTRL key and click,
  then you will jump to the file where that definition appears.  Alternatively,
  you can right-click and then type F12 or Alt-F12.
  For this particular definition, the relevant file is 
  <span class="path">mathlib/data/nat/basic.lean</span>.  Note that we did not
  explicitly import <span class="code">data.nat.basic</span>, but we
  imported <span class="code">data.nat.prime</span>, which imports
  <span class="code">data.nat.sqrt</span>, which imports
  <span class="code">data.nat.basic</span>.  Some standard properties of
  factorials are proved in the same place.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 let p := min_fac m,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 This line defines $p$ using the function <span class="code">min_fac</span>
 defined in <span class="path">mathlib/data/nat/basic.lean</span>.  This is
 supposed to be defined by the requirement that
 <span class="code">min_fac k</span> is the smallest $d>1$ such that $d$
 divides $k$.  This makes sense for $k=0$ (with
 <span class="code">min_fac 0 = 2</span>) and for $k>1$, but this
 characterisation would leave <span class="code">min_fac 1</span> undefined.
 The approach taken by the Lean library is to arbitrarily define 
 <span class="code">min_fac 1 = 1</span>.  This of course means that some
 theorems about the properties of <span class="code">min_fac</span> will
 need auxiliary hypotheses.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 have m_gt_1 : m > 1, {apply nat.succ_lt_succ,apply fact_pos},
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 We now want to show that $m>1$.  We use the keyword
 <span class="code">have</span> to state this fact, and introduce the name
 <span class="code">m_gt_1</span> for it.  (It is possible to reorganise
 the proof to avoid introducing names for minor intermediate facts like this,
 and many experts seem to prefer that style.  However, we feel that such
 names make it much easier for the neophyte to understand what is happening.)
 The proof of <span class="code">m_gt_1</span> involves two ingredients:
 <ul>
  <li>The fact that $n!>0$, which is proved in
   <span class="path">mathlib/data/nat/basic.lean</span> under the name
   <span class="code">fact_pos</span>.
  </li>
  <li>The fact that $a>b$ implies $a+1>b+1$.  This does not come from mathlib,
   but from the core Lean library.  The relevant file is
   <span class="path">lib/lean/library/init/data/nat/lemmas.lean</span>
   under the main directory of the Lean installation, which may well be
   a system directory rather than a user directory.  The name of this
   fact is <span class="code">succ_lt_succ</span>.  (Here
   <span class="code">lt</span> stands for "less than", and
   <span class="code">succ</span> refers to the successor operation
   $a\mapsto a+1$.  As in Peano arithmetic, addition is actually defined in
   terms of the successor operation rather than the other way around.)
  </li>
  In VS Code, it is illuminating to click in various places in the above
  line and examine how the goal state changes as we state the claim that
  $m>1$, use <span class="code">succ_lt_succ</span> to reduce to the claim
  that $n!>0$, and then appeal to <span class="code">fact_pos</span> to prove
  the reduced claim.  Note also that the keyword
  <span class="code">apply</span> refers to a "tactic", which manipulates
  the goal state.  Proof tactics in general are described in Chapter 5 of
  the book
  <a href="https://leanprover.github.io/theorem_proving_in_lean/">Theorem
  Proving in Lean</a>.  One can hover over the word
  <span class="code">apply</span> to see some information about how this
  tactic works.
 </ul>
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 have m_ne_1 : m ≠ 1 := ne_of_gt m_gt_1,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 We now deduce that $m\neq 1$.  This uses the result named
 <span class="code">ne_of_gt</span>, which says that
 $a>b\Rightarrow a\neq b$.  Systems like Lean are set up so that a proof of
 $P\Rightarrow Q$ is essentially the same thing as a function from proofs of
 $P$ to proofs of $Q$.  Here <span class="code">m_gt_1</span> is a proof
 that $m>1$, and we are applying <span class="code">ne_of_gt</span> to it to
 get a proof that $m\neq 1$.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 have p_gt_0 : p > 0, {apply min_fac_pos},
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 We now state that $p>0$, attach the name <span class="code">p_gt_0</span>
 to this claim, and prove it by applying the theorem named
 <span class="code">min_fac_pos</span> from
 <span class="path">prime.lean</span>.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 have p_prime : prime p := min_fac_prime m_ne_1,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 We now state that $p$ is prime, attach the name <span class="code">p_prime</span>
 to this claim, and prove it by applying the theorem named
 <span class="code">min_fac_prime</span> from
 <span class="path">prime.lean</span>.
 <br/><br/>
 Recall that <span class="code">min_fac n</span> was arbitrarily defined to be
 $1$ when $n=1$, so the theorem that <span class="code">min_fac n</span> is prime
 is only valid with the side condition that $n\neq 1$.  The theorem
 <span class="code">min_fac_prime</span> is essentially a function that takes
 as input a natural number $n$ together with a proof that $n\neq 1$, and produces
 a proof that <span class="code">min_fac n</span> is prime.  However, things are
 set up in such a way that a proof of $n\neq 1$ contains the value of $n$ as part
 of the data, so we do not need to supply $n$ explicitly.  This kind of thing
 is handled by Lean's framework of implicit arguments.  The declaration of
 <span class="code">min_fac_prime</span> has the shape
 <div class="code">
  theorem min_fac_prime {n : ℕ} (n1 : n ≠ 1) : prime (min_fac n) := ...
 </div>
 with the curly brackets around <span class="code">{n : ℕ}</span> indicating that
 $n$ will be determined from the context.  (If for some reason we want to supply
 $n$ explicitly, we can use the notation <span class="code">@min_fac_prime</span>
 instead of <span class="code">min_fac_prime</span>.)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 have not_p_le_n : ¬ p ≤ n, {
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 We now state and prove the negation of $p\leq n$.  It is part of the basic logical
 framework of Lean that a proof of this negation is the same as a procedure that
 takes a hypothetical proof of $p\leq n$ and produces a contradiction.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
  intro p_le_n,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 This line means: "let <span class="code">p_le_n</span> be a hypothetical proof
 that $p\leq n$".  Given such a hypothetical proof, we need to produce a contradiction.  
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
  have d0 : p ∣ fact n := dvd_fact p_gt_0 p_le_n,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  We now prove that $p$ divides $n!$.  The proof appeals to the fact (named
  <span class="code">dvd_fact</span>) that $a$ divides
  $b!$ whenever $a>0$ and $a\leq b$.  We supply the explicit arguments
  <span class="code">p_gt_0</span> and <span class="code">p_le_n</span> to
  verify the hypotheses; the implicit arguments $p$ and $n$ are deduced from
  the context. 
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
  have d1 : p ∣ fact n + 1 := min_fac_dvd m,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 We now claim that $p$ divides $m=n! + 1$.  As $p$ was defined to be
 <span class="code">min_fac m</span>, this amounts to the claim that the
 <span class="code">min_fac</span> function was correctly defined.  This was proved in
 <span class="code">prime.lean</span> under the name
 <span class="code">min_fac_dvd</span>.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
  have d  : p ∣ 1 := (nat.dvd_add_iff_right d0).mpr d1,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 We now want to prove that $p$ divides $1$.  For this we appeal to the fact that
 if $a$ divides $b$, then $a$ divides $c$ iff $a$ divides $b+c$.  This fact has
 the name <span class="code">dvd_add_iff_right</span>.  Unfortunately, there are
 two versions of this fact that are currently visible.  One of them comes from
 the file <span class="path">lean/library/init/algebra/ring.lean</span>, and applies
 to an arbitrary commutative ring.  The other comes from
 <span class="path">lean/library/init/data/nat/lemmas.lean</span>, and
 applies only to <span class="code">ℕ</span> (which is a semiring rather than a ring).
 Note that both of these are in the core Lean library, not in mathlib.  We need to
 use the version for <span class="code">ℕ</span>, so we need to resolve the
 ambiguity by providing the explicit prefix in
 <span class="code">nat.dvd_add_iff_right</span>.
 <br/><br/>
 By applying <span class="code">nat.dvd_add_iff_right</span> to
 <span class="code">d0</span>, we obtain a proof that $p$ divides $n!+1$ iff $p$
 divides $1$.  The syntax <span class="code">(...).mpr</span> extracts the
 right-to-left half of this equivalence, which we can then apply to the fact
 <span class="code">d1</span> to obtain a proof that $p$ divides $1$.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
  exact prime.not_dvd_one p_prime d
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 Our goal is to produce a contradiction, or equivalently to prove the proposition
 <span class="code">false</span>.  We do this using the keyword
 <span class="code">exact</span> (which is the name of a kind of tautological tactic)
 followed by an expression that evaluates to <span class="code">false</span>.  The
 theorem <span class="code">prime.not_dvd_one</span> says that no prime divides $1$.
 Equivalently, it is a function that accepts a proof that a number is prime, together
 with a proof that that number divides $1$, and produces
 <span class="code">false</span>.  We can thus apply
 <span class="code">prime.not_dvd_one</span> to the ingredients
 <span class="code">p_prime</span> and <span class="code">d</span> to obtain the
 required contradiction.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 },
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 have p_gt_n : p > n := lt_of_not_ge not_p_le_n,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 We now use the result <span class="code">lt_of_not_ge</span> to convert our proof
 of <span class="code">¬ p ≤ n</span> to a proof of $p > n$.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 existsi p,split,exact p_prime,exact p_gt_n
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 We are now ready to wrap up.  The proof goal is to prove that there exists a number
 with certain properties.  We use the <span class="code">existsi</span> tactic to
 introduce the number that we claim has the relevant properties.  This changes the
 proof goal: we now need to prove that $p$ is prime and $p>n$.  These two claims are
 initially combined as the single goal <span class="code">(prime p) ∧ (p > n)</span>.
 We use the <span class="code">split</span> tactic to divide this into two goals
 <span class="code">prime p</span> and <span class="code">p > n</span>.  We have
 already proved these two facts under the names <span class="code">p_prime</span>
 and <span class="code">p_gt_n</span>, so we can just use the
 <span class="code">exact</span> tactic twice to complete the proof.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
end
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

#check larger_prime
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Lean accepts correct proofs without explicit acknowledgement.  To
get more positive feedback, we can enter
<span class="code">#check larger_prime</span>: this will restate
the fact that we have proved in the message window.

~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

