/-
Free Markov categories, Stage 7: the cited result C1 (Joyal–Street, Theorem 2.3) for the
combinatorial diagrams of Stage 1, and the unconditional forms of the main theorems.

* `Embedding`, `Laws`, `Laws2`, `FsCat`: the laws of `F_s(G)` on classes of diagrams and the
  symmetric strict monoidal category `FsC G`, without C1; the strict functor `Syn_s(G) → F_s(G)`.
* `ArrowAlg`, `Perm`, `Perm2`: permutations of wires in a symmetric strict monoidal category
  (coherence for symmetries).
* `Steps`, `Steps2`, `Passive`: the value of a diagram computed node by node, its independence of
  the order of the nodes (Joyal–Street, Proposition 2.1) and of renaming.
* `Value`, `ValueOps`: the value of a class of diagrams in `Syn_s(G)`, compatible with the
  operations (Joyal–Street, Theorem 2.2); injectivity of `Syn_s(G) → F_s(G)`.
* `Generation`: surjectivity of `Syn_s(G) → F_s(G)`.
* `JoyalStreet`: `JoyalStreet.ofCombinatorial G : JoyalStreet G`, `joyalStreet G`, and the
  namespace `Combinatorial` with Theorems 2.3, 4.1, Lemmas 4.4, 4.5, Proposition 6.6 and
  Theorem 6.7 without C1.
-/
module

public import FreeMarkov.Stage7.Embedding
public import FreeMarkov.Stage7.Laws
public import FreeMarkov.Stage7.Laws2
public import FreeMarkov.Stage7.FsCat
public import FreeMarkov.Stage7.ArrowAlg
public import FreeMarkov.Stage7.Perm
public import FreeMarkov.Stage7.Perm2
public import FreeMarkov.Stage7.Steps
public import FreeMarkov.Stage7.Steps2
public import FreeMarkov.Stage7.Passive
public import FreeMarkov.Stage7.Value
public import FreeMarkov.Stage7.ValueOps
public import FreeMarkov.Stage7.Generation
public import FreeMarkov.Stage7.JoyalStreet
