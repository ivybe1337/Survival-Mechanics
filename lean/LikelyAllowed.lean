import LikelyAllowed.Residual
import LikelyAllowed.Moore
import LikelyAllowed.Canonical
import LikelyAllowed.Joint
import LikelyAllowed.Predictive
import LikelyAllowed.ShortFutures
import LikelyAllowed.Independence
import LikelyAllowed.Conditioned
import LikelyAllowed.Exactness
import LikelyAllowed.Decisions
import LikelyAllowed.Lookahead
import LikelyAllowed.Planning
import LikelyAllowed.Certificates
import LikelyAllowed.Nondet
import LikelyAllowed.Succinct
import LikelyAllowed.Support

/-!
# Likely and Allowed

Machine-checked proofs for *Likely and Allowed: The Joint State of Prediction and Admissibility*
(Joshua Matthew Carter, v1.0, November 2026).

Vocabulary, as in the paper: an *admissibility rule* is `V : List α → Bool`; the *residual set*
`resSet V h` is `R_V(h) = {z | V (h ++ z) = true}`; the *residual state* `κ` is the class of `h`
under `ResEquiv V`; the *predictive state* `ε` is the class under `Process.EpsEquiv`; the *joint
state* `J = (ε, κ)` is the class under `Process.JEquiv`. `AdmMonotone V` says death is absorbing.
`Process.survProb` is the survival probability `S_n` of Section 5 and `Process.condLaw` the
survival-conditioned forecast `Q_n`.

In every file, `Paper X` refers to result `X` of that paper.
-/
