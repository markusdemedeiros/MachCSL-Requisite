# Requisiteness in HeapLang

For HeapLang, the proof has two parts: **show that ownership of a local state lets us simulate every physical step, then use that simulation to build a `wp` proof by Löb induction.** I checked the accompanying Rocq development; its requisiteness proof uses a particularly direct representation of state ownership.

The statement, suppressing ghost names and observation bookkeeping, is:

\[
\operatorname{safe}_{\varphi}(e,\sigma_l)
\quad\Longrightarrow\quad
S_\circ(\sigma_l)\vdash
\operatorname{WP}e\{v.\lceil\varphi(v)\rceil\}.
\]

We start with an operational safety fact and ownership of the corresponding local state. The objective is to construct the semantic `WP`. This is the specialization of the paper’s Theorem 31. [§10](https://iris-project.org/pdfs/2026-icfp-completeness.pdf#page=24)

**First, choose state ownership that captures everything the semantics remembers.**

A HeapLang state contains a heap and a set of allocated prophecy identifiers. The Rocq proof defines, schematically,

\[
S_\circ(\sigma_l,\kappa)=
\left(\mathop{*}_{\ell\mapsto ov\in\sigma_l.\mathrm{heap}}
  \operatorname{pointsto}_{\mathrm{internal}}(\ell,1,ov)\right)
*
\left(\mathop{*}_{p\in\sigma_l.\mathrm{usedProph}}
  \operatorname{proph}(p,\operatorname{resolves}(\kappa,p))\right).
\]

Here \(ov\) is either a live value or a tombstone. **Freed cells remain represented and owned.** This records that their addresses cannot be allocated again.

Combining this ownership with the physical state interpretation gives:

\[
S_\bullet(\sigma,\kappa)*S_\circ(\sigma_l,\kappa_l)
\vdash
\left\lceil
\sigma_l.\mathrm{heap}\subseteq\sigma.\mathrm{heap}
\;\land\;
\sigma_l.\mathrm{usedProph}\subseteq\sigma.\mathrm{usedProph}
\right\rceil.
\]

Heap inclusion includes agreement on stored values and tombstones. The physical heap may contain additional cells. The proof also reconciles the locally recorded prophecy predictions with the physical interpretation’s observation trace. These are `own_state_agree` and `own_state_canonicalize`. [HeapLang proof](https://gitlab.mpi-sws.org/johannes/iris-completeness/-/blob/master/theories/case_studies/heaplang/requisiteness.v)

**Next, establish the step simulation.**

Assume \(e\) is reducible in \(\sigma_l\), and we own both state predicates. We must establish:

1. \(e\) is reducible in the physical state \(\sigma\).
2. For **every** physical step
   \[
   (e,\sigma)\xrightarrow{\kappa}(e',\sigma',\vec e_f),
   \]
   there exists a local successor \(\sigma_l'\) with
   \[
   (e,\sigma_l)\xrightarrow{\kappa}(e',\sigma_l',\vec e_f),
   \]
   and we can update our resources to
   \(S_\bullet(\sigma')*S_\circ(\sigma_l')\).

The expressions, observations, and forked threads match exactly; the two successor states can differ.

The HeapLang cases explain why this works:

| Operation | Reason the physical step can be matched locally |
|---|---|
| Pure computation and `fork` | Their behavior is independent of the heap. |
| Load | Local ownership establishes the same stored value in both heaps. |
| Store, exchange, CAS, FAA | Agreement determines the same result; full ownership permits updating the authoritative heap and local fragment together. |
| Free | Update the cell to a tombstone in both heaps and retain ownership of it. |
| Allocation | An address block fresh in the physical heap is also fresh in its local subheap. Allocate the **same block** locally and obtain its ownership. |
| New prophecy | A physically fresh identifier is also locally fresh. |
| Resolve | Local reducibility supplies ownership of an existing prophecy; match the wrapped operation and consume the same prophecy observation. |

Allocation illustrates the quantifiers: a locally fresh address might already be occupied physically. We therefore first prove that *some* physical allocation is possible, then match whichever physical allocation occurs. We never demand that an arbitrarily chosen local allocation work physically.

The code proves this as `own_state_update` for base steps. Evaluation-context lemmas lift it to arbitrary expression steps. [HeapLang simulation](https://gitlab.mpi-sws.org/johannes/iris-completeness/-/blob/master/theories/case_studies/heaplang/requisiteness.v), [context lifting](https://gitlab.mpi-sws.org/johannes/iris-completeness/-/blob/master/theories/framework/requisite/ectx_lang_requisiteness.v)

**Finally, use the simulation to prove `WP` for concurrent execution.**

Allocate ghost state representing the thread pool and an invariant with contents

\[
\exists T,\sigma_l.\;
S_\circ(\sigma_l)
*
\operatorname{AuthThreads}(T)
*
\lceil\operatorname{safe\text{-}tp}_\varphi(T,\sigma_l)\rceil.
\]

Each thread owns a token \(i\mapsto e\). Prove by Löb induction, uniformly in \(i,e\),

\[
\operatorname{Inv}*i\mapsto e
\vdash
\operatorname{WP}e\{v.\;i\mapsto v\}.
\]

For a value, return its token. Otherwise:

- Unfold `WP` through its lifting lemma, receiving the physical state interpretation.
- Open the invariant. Token agreement identifies the current expression in \(T\); safety gives local reducibility.
- Apply the simulation to obtain physical reducibility and a matching local successor for every physical step.
- Update the thread map, creating tokens for newly forked threads. Safety is preserved by the matching local thread-pool step.
- Restore the invariant and physical state interpretation.
- The step has discharged the guarding later, so apply the Löb hypothesis to the continuing thread and every child.

For the initial thread, start with token \(0\mapsto e\). When it returns \(v\), reopen the invariant: token agreement says the main thread now contains \(v\), so the invariant’s safety fact yields \(\varphi(v)\). This finishes the desired postcondition. [Generic requisiteness proof](https://gitlab.mpi-sws.org/johannes/iris-completeness/-/blob/master/theories/framework/requisite/lang_requisiteness.v)
