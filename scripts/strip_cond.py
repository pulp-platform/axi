import re, sys
inp, outp = sys.argv[1], sys.argv[2]
out = []
depth_tc = 0          # paren depth tracking inside TIMINGCHECK
in_tc = False
tc_start_depth = 0
depth = 0
stripped = 0

def paren_delta(s):
    return s.count("(") - s.count(")")

with open(inp) as f:
    for line in f:
        # detect entering TIMINGCHECK
        if "(TIMINGCHECK" in line:
            in_tc = True
            tc_start_depth = depth
        # only strip COND when NOT inside a timing-check block
        if not in_tc:
            m = re.search(r'\(\s*COND\b.*?(\(IOPATH\b.*\))\s*\)\s*$', line)
            if m:
                indent = line[:len(line)-len(line.lstrip())]
                line = indent + m.group(1) + "\n"
                stripped += 1
        out.append(line)
        depth += paren_delta(line)
        # exiting TIMINGCHECK when we return to its start depth
        if in_tc and depth <= tc_start_depth:
            in_tc = False

open(outp, "w").writelines(out)
print("stripped:", stripped, " remaining COND:", sum(l.count("COND") for l in out))
