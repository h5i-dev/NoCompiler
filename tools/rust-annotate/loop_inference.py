"""Propose affine invariants for natural RV64 loops with constant stride."""

from collections import defaultdict, deque
import re

BRANCHES = {"beq", "bne", "beqz", "bnez", "blt", "bltu", "bge", "bgeu"}
LABEL = re.compile(r"([\w.$]+):$")
MEMORY = re.compile(r"(-?(?:0x[\da-fA-F]+|\d+))\((\w+)\)")
LOADS = {"lb": 1, "lbu": 1, "lh": 2, "lhu": 2, "lw": 4, "lwu": 4, "ld": 8}
STORES = {"sb": 1, "sh": 2, "sw": 4, "sd": 8}
SIZE = re.compile(r"\s*\.size\s+([^,]+),")


def affine(left, right, scale=1):
    if left is None or right is None:
        return None
    result = left.copy()
    for variable, coefficient in right.items():
        result[variable] = result.get(variable, 0) + scale * coefficient
    return {variable: coefficient for variable, coefficient in result.items() if coefficient}


def constant(value):
    return {"": value} if value else {}


def operand(state, register):
    return {} if register in ("zero", "x0") else state.get(register)


def memory_key(state, address):
    if match := MEMORY.fullmatch(address):
        value = affine(operand(state, match[2]), constant(int(match[1], 0)))
        if value:
            bases = value.keys() - {""}
            if len(bases) == 1:
                base, = bases
                if value[base] == 1:
                    return base, value.get("", 0)
    return None


def memory_transfer(state, op, register, address):
    key = memory_key(state, address)
    if op in LOADS:
        if register not in ("zero", "x0"):
            state[register] = state.get(key) if LOADS[op] == 8 else None
        return
    value = operand(state, register)
    for stored in tuple(state):
        if isinstance(stored, tuple):
            # Distinct symbolic bases can alias. Keep only provably disjoint
            # offsets based on the very same address.
            if key is None or stored[0] != key[0] or (
                key[1] < stored[1] + 8 and stored[1] < key[1] + STORES[op]
            ):
                del state[stored]
    if key is not None and STORES[op] == 8 and value is not None:
        state[key] = value


def transfer(state, instruction, opaque=None):
    op, *args = instruction
    if op in BRANCHES or op in {"j", "ret"}:
        return True
    if op in LOADS or op in STORES:
        if len(args) != 2:
            return False
        memory_transfer(state, op, *args)
        return True
    if not args or op not in {
        "li", "mv", "addi", "slli", "add", "sub", "lb", "lbu", "lh",
        "lhu", "lw", "lwu", "ld", "seqz", "snez", "and", "or", "xor",
        "andi", "ori", "xori", "slt", "sltu", "sltiu", "srli", "srai",
        "zext.b", "lui", "auipc", "mul", "not",
    }:
        return False
    dst, *src = args
    try:
        if op == "li":
            result = constant(int(src[0], 0))
        elif op == "mv":
            result = operand(state, src[0])
        elif op == "addi":
            result = affine(operand(state, src[0]), constant(int(src[1], 0)))
        elif op == "slli":
            shift = int(src[1], 0)
            if not 0 <= shift < 64:
                return False
            result = affine({}, operand(state, src[0]), 1 << shift)
        elif op == "andi" and opaque is not None and int(src[1], 0) in (1, 3, 7, 15):
            result = {opaque: 1}
        elif op in {"add", "sub"}:
            result = affine(operand(state, src[0]), operand(state, src[1]), 1 if op == "add" else -1)
        else:
            result = None  # Non-affine result.
    except (IndexError, ValueError):
        return False
    if dst not in ("zero", "x0"):
        state[dst] = result
    return True


def render(expression):
    parts = []
    for name, coefficient in sorted(expression.items()):
        magnitude = abs(coefficient)
        term = name if magnitude == 1 and name else f"{magnitude}{name}"
        if parts:
            parts.append((" + " if coefficient > 0 else " - ") + term)
        else:
            parts.append(("-" if coefficient < 0 else "") + term)
    return "".join(parts) or "0"


def parse_body(lines):
    labels = {}
    instructions = []
    for line_number, line in enumerate(lines):
        code = line.partition("#")[0].strip()
        if label := LABEL.fullmatch(code):
            labels[label[1]] = (len(instructions), line_number)
        elif code and not code.startswith("."):
            instructions.append(re.split(r"[\s,]+", code))
    return instructions, labels


def control_flow(instructions, labels):
    successors = {}
    for index, (op, *args) in enumerate(instructions):
        edges = set()
        if op in BRANCHES or op == "j":
            target = labels.get(args[-1]) if args else None
            if target is not None and target[0] < len(instructions):
                edges.add(target[0])
        if op not in {"j", "ret", "tail", "jr", "unimp"} and index + 1 < len(instructions):
            edges.add(index + 1)
        successors[index] = edges

    reachable = set()
    pending = [0] if instructions else []
    while pending:
        node = pending.pop()
        if node not in reachable:
            reachable.add(node)
            pending.extend(successors[node])
    predecessors = {node: set() for node in reachable}
    for source in reachable:
        for target in successors[source]:
            predecessors[target].add(source)
    return predecessors


def natural_loops(predecessors):
    if not predecessors:
        return {}, {}
    dominators = {node: set(predecessors) for node in predecessors}
    dominators[0] = {0}
    changed = True
    while changed:
        changed = False
        for node in sorted(predecessors.keys() - {0}):
            result = {node} | set.intersection(*(dominators[p] for p in predecessors[node]))
            if result != dominators[node]:
                dominators[node] = result
                changed = True

    latches = defaultdict(set)
    for node, sources in predecessors.items():
        latches[node].update(p for p in sources if node in dominators[p])
    latches = {head: sources for head, sources in latches.items() if sources}
    bodies = {}
    for head, sources in latches.items():
        body = {head}
        pending = list(sources)
        while pending:
            node = pending.pop()
            if node not in body:
                body.add(node)
                pending.extend(predecessors[node])
        bodies[head] = body
    return latches, bodies


def order_nodes(predecessors, latches):
    pending = {node: preds - latches.get(node, set()) for node, preds in predecessors.items()}
    successors = defaultdict(list)
    for node, preds in pending.items():
        for pred in preds:
            successors[pred].append(node)
    ready = deque(sorted(node for node, preds in pending.items() if not preds))
    order = []
    while ready:
        node = ready.popleft()
        order.append(node)
        for successor in successors[node]:
            pending[successor].remove(node)
            if not pending[successor]:
                ready.append(successor)
    return order if len(order) == len(predecessors) else []


def merge(states):
    if not states:
        return {}
    return {
        reg: value for reg, value in states[0].items()
        if value is not None and all(state.get(reg) == value for state in states[1:])
    }


def merge_slice_relations(states, merged, slices, node):
    """Keep a common slice endpoint when incoming paths consume different prefixes."""
    if len(states) < 2:
        return {}, [], [], []
    inferred = {}
    variables = []
    bounds = []
    origins = []
    common = {reg for reg in set.intersection(*(set(state) for state in states)) - set(merged)
              if isinstance(reg, str)}
    for base, length, stride in slices:
        for cursor in sorted(common - inferred.keys()):
            for cursor_base in ({base: 1}, {}):
                offsets = [affine(state[cursor], cursor_base, -1) for state in states]
                if any(offset is None or offset.keys() - {""} for offset in offsets):
                    continue
                distances = [offset.get("", 0) for offset in offsets]
                if any(distance < 0 or distance % stride for distance in distances):
                    continue
                consumed = [distance // stride for distance in distances]
                for count in sorted(common - inferred.keys() - {cursor}):
                    for count_base in ({length: 1}, {}):
                        if not all(state[count] == affine(count_base, constant(amount), -1)
                                   for state, amount in zip(states, consumed)):
                            continue
                        name = f"prefix{node}_{len(variables)}"
                        variables.append(name)
                        bounds.append(f"{min(consumed)} <= {name} <= {max(consumed)}")
                        inferred[cursor] = {**cursor_base, name: stride}
                        inferred[count] = {**count_base, name: -1}
                        origins.append((name, length))
                        break
                    if cursor in inferred:
                        break
                if cursor in inferred:
                    break
    return inferred, variables, bounds, origins


def written_registers(instructions, registers):
    written = set()
    for instruction in instructions:
        state = {reg: {reg: 1} for reg in registers}
        if not transfer(state, instruction):
            return registers.copy()
        written.update(reg for reg in registers if state[reg] != {reg: 1})
    return written


def recurrence(instructions, head, latch, body, order, predecessors, latches, writes, registers):
    states = {}
    for node in order:
        if node not in body:
            continue
        if node == head:
            state = {reg: {reg: 1} for reg in registers}
        else:
            preds = predecessors[node] - latches.get(node, set())
            state = merge([states[p] for p in preds if p in states])
            # Values modified by an inner loop cannot be assumed equal on exit.
            for register in writes.get(node, ()):
                state.pop(register, None)
        if node == latch:
            return state
        if not transfer(state, instructions[node], f"step{node}"):
            return {}
        states[node] = state
    return {}


def candidate(entry, lengths, post, instruction, remaining, join_vars, tail_vars, opaque, accesses):
    op, *args = instruction
    lower = 1
    if op == "bnez" and len(args) == 2:
        left, right = args[0], "zero"
    elif op == "bne" and len(args) == 3:
        left, right = args[:2]
    elif op == "bgeu" and len(args) == 3:
        right, left = args[:2]
    else:
        return None

    # Recover the value at the head from each latch operand. A temporary is
    # allowed when it holds the updated value of a loop-carried register.
    def old_value(reg):
        if reg in ("zero", "x0"):
            return {}, {}
        update = post.get(reg)
        for carried, initial in entry.items():
            if initial is not None and post.get(carried) == update and update is not None:
                delta = affine(update, {carried: 1}, -1)
                if set(delta) <= {""}:
                    return initial, delta
        return None, None

    initial_left, step_left = old_value(left)
    initial_right, step_right = old_value(right)
    initial = affine(initial_left, initial_right, -1)
    delta = affine(step_left, step_right, -1)
    if initial is None or delta is None or set(delta) != {""}:
        return None
    stride = -delta[""]
    scale = stride
    if op == "bgeu":
        # LLVM often compares the updated cursor with (end - step) to
        # ensure one more full iteration fits.
        if step_left != constant(-stride) or step_right or stride >= 0:
            return None
        lower = -stride
        initial = affine(initial, constant(stride))
        scale = -1
    if any(coefficient % scale for coefficient in initial.values()):
        return None
    trip_count = {name: coefficient // scale for name, coefficient in initial.items()}
    length = next((n for n in lengths if trip_count.get(n) == 1 and all(
        name == n or name in opaque or
        (name in join_vars and join_vars[name] == n and coefficient == -1) or
        (name == "" and coefficient <= 0)
        for name, coefficient in trip_count.items()
    )), None)
    if length is None and len(trip_count) == 1:
        name, coefficient = next(iter(trip_count.items()))
        if coefficient == 1:
            length = tail_vars.get(name)
    if length is None:
        return None

    inferred = {}
    alignment = []
    for reg, start in entry.items():
        step = affine(post.get(reg), {reg: 1}, -1)
        if not isinstance(reg, str) or start is None or not step or set(step) != {""} or reg == "sp" or step[""] % lower:
            continue
        expression = affine(start, {**trip_count, remaining: -1}, step[""] // lower)
        if not (expression.keys() & (join_vars.keys() | tail_vars.keys() | opaque | {"entrysp"})):
            inferred[reg] = expression
            for width, offset in accesses.get(reg, ()):
                if step[""] % width == 0 and op == "bgeu":
                    aligned = render(affine(expression, constant(offset)))
                    alignment.append(f"{width} | ({aligned})")
    if not inferred:
        return None
    types = [f"{reg}: int({render(expression)})" for reg, expression in inferred.items()]
    bounds = [f"{lower} <= {remaining} <= {length}", *sorted(set(alignment))]
    return inferred, (
        f"\t#: inv [{remaining}] {', '.join(types)} "
        f"where {', '.join(bounds)} decreases {remaining}\n"
    )


def variable_stride_candidate(entry, lengths, post, instruction, remaining):
    """Relate a shrinking count to cursors that advance by the same symbolic step."""
    op, *args = instruction
    if op != "bnez" or len(args) != 2:
        return None
    counter = args[0]
    length = next((name for name in lengths if entry.get(counter) == {name: 1}), None)
    delta = affine(post.get(counter), {counter: 1}, -1)
    if length is None or not delta or not (delta.keys() - {""}):
        return None
    term = next(name for name in delta if name)
    scale = delta[term]
    inferred = {}
    for reg, start in entry.items():
        if not isinstance(reg, str) or reg == "sp" or "entrysp" in start:
            continue
        change = affine(post.get(reg), {reg: 1}, -1)
        if not change or change.get(term, 0) % scale:
            continue
        multiple = change.get(term, 0) // scale
        if affine(change, delta, -multiple) == {}:
            inferred[reg] = affine(start, {remaining: 1, length: -1}, multiple)
    if len(inferred) < 2:
        return None
    registers = ", ".join(f"{reg}: int({render(value)})" for reg, value in inferred.items())
    return inferred, (
        f"\t#: inv [{remaining}] {registers} "
        f"where 1 <= {remaining} <= {length} decreases {remaining}\n"
    )


def infer_loops(instructions, labels, seeds):
    predecessors = control_flow(instructions, labels)
    latches, bodies = natural_loops(predecessors)
    if not bodies:
        return {}
    order = order_nodes(predecessors, latches)
    registers_at_entry, lengths, slices = seeds
    registers = {reg for reg in registers_at_entry if isinstance(reg, str)}
    registers.update(arg for _, *args in instructions for arg in args if re.fullmatch(r"[ats]\d+", arg))
    writes = {
        head: written_registers((instructions[node] for node in body), registers)
        for head, body in bodies.items()
    }

    states = {}
    nonzero = {}
    annotations = {}
    loop_vars = {}
    join_vars = {}
    tail_vars = {}
    opaque = set()
    label_lines = dict(labels.values())
    def edge_facts(pred, node):
        facts = nonzero[pred].copy()
        op, *args = instructions[pred]
        if op in {"beqz", "bnez"} and len(args) == 2:
            target = labels.get(args[1])
            value = states[pred].get(args[0])
            if target and target[0] != pred + 1 and (node == target[0]) == (op == "bnez"):
                facts.update(n for n in lengths if value == {n: 1})
        return facts

    for node in order:
        facts = set()
        if node == 0:
            state = registers_at_entry.copy()
        else:
            preds = predecessors[node] - latches.get(node, set())
            incoming = [states[p] for p in sorted(preds)]
            state = merge(incoming)
            expired = {name for head, name in loop_vars.items() if node not in bodies[head]}
            state = {reg: expr for reg, expr in state.items() if not (expr.keys() & expired)}
            facts = set.intersection(*(edge_facts(pred, node) for pred in preds))
            if node not in bodies and node in label_lines and len(preds) > 1:
                inferred, names, bounds, origins = merge_slice_relations(incoming, state, slices, node)
                op, *args = instructions[node]
                if op in {"bgeu", "bltu"} and len(args) == 3 and not inferred:
                    cursor, end = args[:2]
                    if cursor not in state:
                        for base, length, stride in slices:
                            endpoint = {base: 1, length: stride}
                            if (state.get(end) == endpoint and all(
                                isinstance(path.get(cursor), dict) and path[cursor].get(base) == 1
                                for path in incoming
                            )):
                                tail = f"tail{node}"
                                names.append(tail)
                                bounds.append(f"0 <= {tail} <= {stride}{length}")
                                inferred[cursor] = {**endpoint, tail: -1}
                                if stride == 1:
                                    tail_vars[tail] = length
                                break
                if facts or inferred:
                    constraints = ", ".join([*(f"1 <= {n}" for n in sorted(facts)), *bounds])
                    params = f" [{', '.join(names)}]" if names else ""
                    regs = ", ".join(f"{reg}: int({render(expr)})" for reg, expr in inferred.items())
                    annotations[label_lines[node]] = f"\t#: join{params} {regs} where {constraints}\n".replace("join  ", "join ")
                    state.update(inferred)
                    join_vars.update(origins)
        if node in bodies:
            remaining = "remaining" if not annotations else f"remaining{len(annotations)}"
            candidates = []
            for latch in sorted(latches[node]):
                post = recurrence(instructions, node, latch, bodies[node], order,
                                  predecessors, latches, writes, registers)
                accesses = defaultdict(set)
                for inside in bodies[node]:
                    op, *args = instructions[inside]
                    if op in {"ld", "sd", "lw", "lwu", "sw", "lh", "lhu", "sh"} and args:
                        address = re.fullmatch(r"(-?\d+)\((\w+)\)", args[-1])
                        if address:
                            width = {"d": 8, "w": 4, "h": 2}[op[1]]
                            accesses[address[2]].add((width, int(address[1])))
                candidates.append(
                    candidate(state, lengths, post, instructions[latch], remaining,
                              join_vars, tail_vars, opaque, accesses)
                    or variable_stride_candidate(state, lengths, post, instructions[latch], remaining)
                )
            result = candidates[0] if all(item == candidates[0] for item in candidates) else None
            for reg in writes[node]:
                state.pop(reg, None)
            state = {reg: value for reg, value in state.items() if isinstance(reg, str)}
            if result and node in label_lines:
                inferred, text = result
                annotations[label_lines[node]] = text
                loop_vars[node] = remaining
                state.update(inferred)
        name = f"opaque{node}"
        if not transfer(state, instructions[node], name):
            state.clear()
        if any(value == {name: 1} for value in state.values()):
            opaque.add(name)
        states[node] = state
        nonzero[node] = facts
    return annotations


def function_bodies(source, symbols):
    lines = source.splitlines(keepends=True)
    start = None
    for index, line in enumerate(lines):
        if start is None:
            label = LABEL.fullmatch(line.strip())
            if label and label[1] in symbols:
                start = index
                symbol = label[1]
        elif (end := SIZE.match(line)) and end[1] == symbol:
            instructions, labels = parse_body(lines[start:index])
            yield symbol, start, instructions, labels
            start = None


def annotate(source, abi):
    lines = source.splitlines(keepends=True)
    annotations = {}
    for symbol, start, instructions, labels in function_bodies(source, abi):
        for offset, annotation in infer_loops(instructions, labels, abi[symbol]).items():
            annotations[start + offset] = annotation
    return "".join(line + annotations.get(index, "") for index, line in enumerate(lines))
