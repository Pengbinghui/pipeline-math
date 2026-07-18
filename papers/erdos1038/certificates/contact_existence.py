#!/usr/bin/env python3
"""Arb certificate for existence of the contact triple by scalar reduction.

For q in a short rational interval I, the equations F_R(q,u)=0 and
F_L(q,v)=0 have unique roots u(q) and v(q) in prescribed intervals.
The script rigorously brackets these roots at the two endpoints of I and
certifies opposite signs of kappa(q)=K(q,u(q),v(q)).  The intermediate
value theorem then yields a solution of (F_R,F_L,K)=0.

All pass/fail decisions use outward-rounded python-flint Arb arithmetic.
"""

from __future__ import annotations

import os
from decimal import Decimal, getcontext

from flint import arb, ctx

BITS = int(os.environ.get("ERDOS1038_ARB_BITS", "384"))
ctx.prec = BITS
getcontext().prec = 260

Q0 = Decimal("0.94985834582347031848349802544031979")
U0 = Decimal("0.89396612207545611611103128550805002")
V0 = Decimal("0.96455509699582140639698562612728156")
BOX_RAD = Decimal("1e-30")
Q_IVT_RAD = Decimal("1e-31")
BISECT_STEPS = 180


def A(x: Decimal | str | int) -> arb:
    return arb(str(x))


def ball(mid: Decimal, rad: Decimal) -> arb:
    return arb(str(mid), str(rad))


def log(x):
    return x.log()


def Lambda(y):
    return log((1 + y) / (1 - y))


def pfun(q):
    return log(2 / (1 - q * q)) / Lambda(q)


def X(q, y):
    return (2 * q * q - 1 - y * y) / (1 - y * y)


def Xprime(q, y):
    return -4 * y * (1 - q * q) / (1 - y * y) ** 2


def FR(q, u):
    p = pfun(q)
    return Lambda(u) - p * log((q + u) / (q - u))


def FL(q, v):
    p = pfun(q)
    return Lambda(v) - p * log((q + v) / (v - q))


def contact_values(q, u, v):
    p = pfun(q)
    r = X(q, u)
    z = X(q, v)
    C = (
        r * u * Lambda(u)
        - z * v * Lambda(v)
        - (r - z) * p * Lambda(q)
    ) / (v * Lambda(v) - u * Lambda(u))
    FRu = 2 / (1 - u * u) - 2 * p * q / (q * q - u * u)
    FLv = 2 / (1 - v * v) + 2 * p * q / (v * v - q * q)
    K = (
        v * (z + C) * FLv / Xprime(q, v)
        - u * (r + C) * FRu / Xprime(q, u)
    )
    return FR(q, u), FL(q, v), K


def is_positive(x: arb) -> bool:
    return x.lower() > 0


def is_negative(x: arb) -> bool:
    return x.upper() < 0


def require(name: str, condition: bool) -> None:
    if not condition:
        raise AssertionError(name)
    print(f"PASS: {name}")


def bisect_sign_change(q: Decimal, lo: Decimal, hi: Decimal, f, *, low_negative: bool):
    """Bracket a unique root, preserving the certified endpoint signs."""
    q_arb = A(q)
    flo = f(q_arb, A(lo))
    fhi = f(q_arb, A(hi))
    if low_negative:
        require("initial lower endpoint is negative", is_negative(flo))
        require("initial upper endpoint is positive", is_positive(fhi))
    else:
        require("initial lower endpoint is positive", is_positive(flo))
        require("initial upper endpoint is negative", is_negative(fhi))

    for _ in range(BISECT_STEPS):
        mid = (lo + hi) / Decimal(2)
        fm = f(q_arb, A(mid))
        if is_positive(fm):
            if low_negative:
                hi = mid
            else:
                lo = mid
        elif is_negative(fm):
            if low_negative:
                lo = mid
            else:
                hi = mid
        else:
            raise AssertionError(f"bisection sign unresolved at {mid}: {fm}")
    return lo, hi


def enclosure(lo: Decimal, hi: Decimal) -> arb:
    mid = (lo + hi) / Decimal(2)
    rad = (hi - lo) / Decimal(2)
    # Inflate by one ulp at the working Decimal precision before conversion.
    rad += Decimal("1e-240")
    return ball(mid, rad)


def main() -> None:
    q_minus = Q0 - Q_IVT_RAD
    q_plus = Q0 + Q_IVT_RAD
    q_interval = ball(Q0, Q_IVT_RAD)

    u_low, u_high = U0 - BOX_RAD, U0 + BOX_RAD
    v_low, v_high = V0 - BOX_RAD, V0 + BOX_RAD

    pI = pfun(q_interval)
    require("0 < p(q) on I", pI.lower() > 0)
    require("p(q) < q on I", pI.upper() < q_interval.lower())
    require("q < 1 on I", q_interval.upper() < 1)

    fr_low = FR(q_interval, A(u_low))
    fr_high = FR(q_interval, A(u_high))
    fl_low = FL(q_interval, A(v_low))
    fl_high = FL(q_interval, A(v_high))
    require("F_R(q,u_0-1e-30) > 0 uniformly on I", is_positive(fr_low))
    require("F_R(q,u_0+1e-30) < 0 uniformly on I", is_negative(fr_high))
    require("F_L(q,v_0-1e-30) < 0 uniformly on I", is_negative(fl_low))
    require("F_L(q,v_0+1e-30) > 0 uniformly on I", is_positive(fl_high))

    endpoint_data = []
    for label, q in (("q_minus", q_minus), ("q_plus", q_plus)):
        print(f"--- {label} ---")
        ulo, uhi = bisect_sign_change(q, u_low, u_high, FR, low_negative=False)
        vlo, vhi = bisect_sign_change(q, v_low, v_high, FL, low_negative=True)
        uI = enclosure(ulo, uhi)
        vI = enclosure(vlo, vhi)
        kval = contact_values(A(q), uI, vI)[2]
        endpoint_data.append((label, q, uI, vI, kval))
        print(f"u({label}) in {uI}")
        print(f"v({label}) in {vI}")
        print(f"kappa({label}) in {kval}")

    k_minus = endpoint_data[0][4]
    k_plus = endpoint_data[1][4]
    require("kappa(q_minus) > 0", is_positive(k_minus))
    require("kappa(q_plus) < 0", is_negative(k_plus))

    # The IVT solution lies in the original product box.  Use that box to
    # certify all numerical inequalities required later in the manuscript.
    q_box = ball(Q0, BOX_RAD)
    u_box = ball(U0, BOX_RAD)
    v_box = ball(V0, BOX_RAD)
    p = pfun(q_box)
    alpha = 2 * q_box * q_box - 1
    r = X(q_box, u_box)
    z = X(q_box, v_box)
    D = r - z

    facts = [
        ("D < 1.836", D.upper() < A("1.836")),
        ("D < alpha+sqrt(2)", D.upper() < (alpha + A(2).sqrt()).lower()),
        ("0 < D-1.708", (D - A("1.708")).lower() > 0),
        ("D-1.708 < 0.127", (D - A("1.708")).upper() < A("0.127")),
        ("D-1.708 < alpha", (D - A("1.708")).upper() < alpha.lower()),
        ("D-1.708 < 2(1-alpha)", (D - A("1.708")).upper() < (2 * (1 - alpha)).lower()),
        ("2alpha-1-(D-1.708)>0", (2 * alpha - 1 - (D - A("1.708"))).lower() > 0),
        ("kernel lower ratio > 12/25", (1 / (2 + (D - A("1.708")) / 2)).lower() > A(12) / 25),
        ("kernel upper ratio < 1/2", ((D - 1) / (1 + alpha)).upper() < A(1) / 2),
        ("0 < p < q < 1", p.lower() > 0 and p.upper() < q_box.lower() and q_box.upper() < 1),
        ("0 < u < q < v < 1", u_box.lower() > 0 and u_box.upper() < q_box.lower() and q_box.upper() < v_box.lower() and v_box.upper() < 1),
    ]
    for name, ok in facts:
        require(name, ok)

    print("ENCLOSURES FROM THE ORIGINAL PRODUCT BOX:")
    for name, val in (("q", q_box), ("u", u_box), ("v", v_box), ("p", p), ("alpha", alpha), ("r", r), ("z", z), ("D", D)):
        print(f"  {name} = {val}")
    print("PASS: scalar contact existence and all numerical facts")


if __name__ == "__main__":
    main()
