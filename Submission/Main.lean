import Submission.Challenge01
import Submission.Challenge05
set_option linter.all false

namespace Submission

def r : ℕ := 3

theorem challenge_1 : ∀ {V : Type*} [Fintype V] (G : SimpleGraph V), SimpleGraph.hadwigerNumber G ≤ r → G.Colorable r := challenge_1_proof
theorem challenge_5 : ErdosHajnalConjectureFor (SimpleGraph.pathGraph r) := challenge_5_proof

end Submission
