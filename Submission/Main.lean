import Submission.Challenge02
import Submission.Challenge03
import Submission.Challenge04
import Submission.Challenge07
set_option linter.all false

namespace Submission

def r : ℕ := 1
def B : ℕ := 0

theorem challenge_2 : ∀ (p m : ℕ) [Fact p.Prime], 0 < m → p ^ m ≤ r → ExcludedMinorsAtMost p m B := challenge_2_proof
theorem challenge_3 : CaccettaHaggkvistFor r := challenge_3_proof
theorem challenge_4 : ∀ {W V : Type} [Fintype W] [Fintype V] [Nonempty V] (H : SimpleGraph W) (G : SimpleGraph V), BipartiteBoundedBy H r → SidorenkoFor H G := challenge_4_proof
theorem challenge_7 : spherePackingConstant r = latticePackingConstant r := challenge_7_proof

end Submission
