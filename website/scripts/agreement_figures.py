"""Agreement and delegation in the same box vocabulary as execution.

Agents contribute terms; their principals approve the contract and runtime.
Delegation is checked against parent obligations and existing commitments jointly.
"""
from pathlib import Path
from diagram_style import SLATE, RED, GREEN, RULE, MUTED, text, line, box, frame

PURPLE = '#6c5684'


def save(root, name, size, body, description, title):
    (root / 'public/media/site' / f'{name}.svg').write_text(
        frame(*size, body, description, root, title))


def shared_contract(x, y, w, h):
    center = x + w / 2
    result = box(x, y, w, h, '')
    result += text(center, y + 43, 'Shared contract', 22, weight=500)
    result += line(f'M{x+24} {y+66}H{x+w-24}', RULE, width=1)
    for offset, label in [(105, 'Task and resources'), (144, 'Constraints'), (183, 'Completion conditions')]:
        result += text(center, y + offset, label, 21)
    return result


def prepare_formation(root: Path, description: str):
    title = 'One contract approved by both parties'
    d = box(20, 170, 214, 64, 'Traveller agent', 21, weight=500)
    d += box(726, 170, 214, 64, 'Provider agent', 21, RED, 500)
    d += text(127, 277, 'Budget and|disclosure rules', 19, MUTED)
    d += text(833, 277, 'Service and|completion evidence', 19, MUTED)
    d += shared_contract(318, 90, 324, 234)
    d += line('M234 202H318', arrow=True) + line('M726 202H642', arrow=True)
    d += line('M480 324V391', arrow=True)
    d += box(210, 391, 540, 101, '')
    d += text(480, 429, 'Both principals approve', 22, weight=500)
    d += text(480, 465, 'Contract and execution environment', 20)
    save(root, 'contract-formation-desktop', (960, 560), d, description, title)

    m = box(14, 30, 180, 62, 'Traveller agent', 20, weight=500)
    m += box(226, 30, 180, 62, 'Provider agent', 20, RED, 500)
    m += line('M104 92V137H153V181', arrow=True)
    m += line('M316 92V137H267V181', arrow=True)
    m += shared_contract(54, 181, 312, 221)
    m += line('M210 402V477', arrow=True)
    m += box(32, 477, 356, 102, '')
    m += text(210, 509, 'Both principals approve', 21, weight=500)
    m += text(210, 541, 'Contract and execution|environment', 20)
    save(root, 'contract-formation-mobile', (420, 610), m, description, title)


def prepare_delegation(root: Path, description: str):
    title = 'A subtask remains governed by the parent agreement'
    d = text(557, 40, 'Checked against', 18, MUTED)
    d += box(402, 62, 310, 100, 'Parent contract|Existing delegations', 21)
    d += line('M557 162V235', arrow=True)
    d += box(16, 235, 154, 64, 'Provider|agent', 21, RED, 500)
    d += text(93, 335, 'Arrange the trip', 18, MUTED)
    d += line('M170 267H212', arrow=True)
    d += box(212, 225, 217, 84, 'Proposed subcontract|+ proof', 20)
    d += text(320, 345, 'Visa arrangements', 18, MUTED)
    d += line('M429 267H480', arrow=True)
    d += box(480, 235, 154, 64, 'Proof check', 21, weight=500)
    d += line('M634 267H740', GREEN, arrow=True)
    d += text(687, 230, 'Accepted', 18, GREEN)
    d += box(740, 225, 204, 84, 'Approved|subcontract', 21)
    d += line('M842 309V391', arrow=True)
    d += box(740, 391, 204, 64, 'Sub-agent', 20, PURPLE, 500)
    d += text(842, 487, 'Scoped authority', 18, MUTED)
    d += line('M16 528H944', RULE, width=1)
    d += text(480, 571, 'Parent constraints remain in force', 21, SLATE)
    save(root, 'delegation-desktop', (960, 620), d, description, title)

    m = box(24, 44, 160, 64, 'Provider agent', 20, RED, 500)
    m += line('M184 76H222', arrow=True)
    m += box(222, 24, 174, 104, 'Proposed|subcontract|+ proof', 20)
    m += line('M309 128V218', arrow=True)
    m += text(113, 156, 'Checked against', 18, MUTED)
    m += box(24, 175, 178, 104, 'Parent contract|Existing|delegations', 20)
    m += line('M202 250H232', arrow=True)
    m += box(232, 218, 154, 64, 'Proof check', 21, weight=500)
    m += line('M309 282V370', GREEN, arrow=True)
    m += text(287, 333, 'Accepted', 18, GREEN, anchor='end')
    m += box(223, 370, 173, 84, 'Approved|subcontract', 21)
    m += line('M309 454V518', arrow=True)
    m += box(223, 518, 173, 64, 'Sub-agent', 20, PURPLE, 500)
    m += line('M12 615H408', RULE, width=1)
    m += text(210, 647, 'Parent constraints|remain in force', 21, SLATE)
    save(root, 'delegation-mobile', (420, 700), m, description, title)
