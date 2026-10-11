# small algebraic relations between the t = 4 internal diag constants
P = 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001
d = [0x10dc6e9c006ea38b04b1e03b4bd9490c0d03f98929ca1d7fb56821fd19d3b6e7,
     0x0c28145b6a44df3e0149b3d0a30b3bb599df9756d4dd9b84a86b38cfb45a740b,
     0x00544b8338791518b2c7645a50392798b21f75bb60e3596170067d00141cac15,
     0x222c01175718386f2e2e82eb122789e352e105a3b8fa852613bc534433ee428b]
B = 1 << 40


def ratrec(a):
    # a = n/m mod P with n, m about 2^127 (half-gcd stop)
    r0, r1, s0, s1 = P, a % P, 0, 1
    while r1 >= 1 << 127:
        q = r0 // r1
        r0, r1, s0, s1 = r1, r0 - q * r1, s1, s0 - q * s1
    return r1, s1


def small(a):
    a %= P
    return min(a, P - a) < B


cands = {}
for i in range(4):
    cands[f"d{i}"] = d[i]
    cands[f"mu{i}"] = d[i] + 1
names = list(cands)
hits = []
for a in names:
    x = cands[a]
    n, m = ratrec(x)
    if abs(n) * abs(m) < 1 << 80:
        hits.append(f"{a} = {n}/{m}")
    for k in range(-16, 17):
        if small(x + k):
            hits.append(f"{a} + {k} small")
for i, a in enumerate(names):
    for b in names[i + 1:]:
        if a[-1] == b[-1]:
            continue  # d_i and mu_i = d_i + 1
        x, y = cands[a], cands[b]
        for e in range(1, 9):
            for f in range(1, 9):
                if pow(x, e, P) == pow(y, f, P) or pow(x, e, P) * pow(y, f, P) % P == 1:
                    hits.append(f"{a}^{e} = {b}^(+-{f})")
        for k in range(-8, 9):
            for s in (x + k * y, x * k - y):
                if small(s):
                    hits.append(f"{a}, {b}: linear relation with {k}")
        r = x * pow(y, P - 2, P) % P
        n, m = ratrec(r)
        if abs(n) * abs(m) < 1 << 80:
            hits.append(f"{a}/{b} = {n}/{m}")
print("bits:", [x.bit_length() for x in d])
print("hits:", hits or "none")
print("p-1 mod 5:", (P - 1) % 5, " p-1 mod 8:", (P - 1) % 8)
for i in range(4):
    mu = d[i] + 1
    print(f"mu{i} fourth power:", pow(mu, (P - 1) // 4, P) == 1)
