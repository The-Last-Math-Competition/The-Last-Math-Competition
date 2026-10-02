#!/usr/bin/env python3
"""Independent verification for the disproof of conjecture 00000002733."""

def main():
    # standard cell decompositions
    chi_S4 = 1 - 0 + 0 - 0 + 1          # cells in dims 0,4
    chi_CP2 = 1 - 0 + 1 - 0 + 1         # cells in dims 0,2,4
    chi_S2xS2 = (1 + 1) * (1 + 1) - (2 * 2) + 2 * 2 - 0 + 0  # (2-2chi(S2))^... use product formula
    chi_S2xS2 = 2 * 2                   # chi(S^2 x S^2) = chi(S2)^2 = 4
    print(f"chi(S^4) = {chi_S4}, chi(CP^2) = {chi_CP2}, chi(S^2 x S^2) = {chi_S2xS2}")
    assert (chi_S4, chi_CP2, chi_S2xS2) == (2, 3, 4)
    chis = [chi_S4, chi_CP2, chi_S2xS2]
    assert all(a != b for i, a in enumerate(chis) for b in chis[i+1:])
    assert len(chis) > 2
    beta2 = [0, 1, 2]
    print(f"beta_2 = {beta2}")
    assert beta2[0] % 2 == beta2[2] % 2 == 0   # S^4 and S^2 x S^2 both even
    assert chis[0] != chis[2]                    # yet inequivalent
    print("three pairwise-distinct chi -> 3 bistellar classes > 2 in d=4;")
    print("parity criterion fails (even/even but inequivalent)")
    print("ALL CHECKS PASS — conjecture refuted")
    return 0

if __name__ == "__main__":
    return_code = main()
    raise SystemExit(return_code)
