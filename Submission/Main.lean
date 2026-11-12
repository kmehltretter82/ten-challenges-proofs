import Submission.Challenge05R4
set_option linter.all false

namespace Submission

def r : ℕ := 4

theorem challenge_5 : ErdosHajnalConjectureFor (SimpleGraph.pathGraph r) := challenge_5_r4_proof

end Submission
