import Submission.Challenge04R2
set_option linter.all false

namespace Submission

def r : ℕ := 2

theorem challenge_4 : ∀ {W V : Type} [Fintype W] [Fintype V] [Nonempty V] (H : SimpleGraph W) (G : SimpleGraph V), BipartiteBoundedBy H r → SidorenkoFor H G := challenge_4_r2_proof

end Submission
