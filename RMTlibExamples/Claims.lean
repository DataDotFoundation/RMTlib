import RMTlib

/-!
# RMTlib's claims, checked against the corpus (RMTlib#56)

`RMT.Claims` states RMTlib's hedgehog, junction and fox claims. This gate fails the build if any
claim overclaims (declares more maturity than its Lean statements support) or has a problem (a
missing statement, or a junction without one).
-/

#guard_msgs (drop info) in
#claim_report in RMT.Claims expect (overclaims := 0) (problems := 0)
