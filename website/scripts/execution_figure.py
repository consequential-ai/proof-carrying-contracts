"""Responsive execution schematic; coordinates follow the main action sequence.

Keep the executing agent, proposed call and checker within the runtime boundary.
Context is a separate input; the recorded result becomes the next check's state.
Every check returns feedback to the agent through the lower return path.
The retained Geist subset makes standalone SVG labels match the website.
"""
from pathlib import Path
from diagram_style import SLATE, RED, GREEN, RULE, MUTED, text, line, box, frame


def prepare_execution(root: Path, description: str):
    # Desktop: a single action sequence; every runtime component is inside.
    d = '<g id="airlock">' + line('M16 20H724V462H16Z', SLATE, width=1.4) + '</g>'
    d += text(42, 61, 'Airlock', 26, weight=500, anchor='start')
    d += text(42, 87, 'Controlled runtime', 17, MUTED, anchor='start')
    d += text(862, 61, 'Outside the Airlock', 17, MUTED)
    d += '<g id="executing-agent">' + box(44, 251, 128, 60, 'Agent', stroke=RED, weight=500) + '</g>'
    d += line('M172 281H218', arrow=True)
    d += box(218, 251, 194, 60, 'Action + proof')
    d += line('M412 281H497', arrow=True)
    d += text(582, 83, 'Checked against', 18, MUTED)
    d += box(450, 97, 264, 98, 'Contract|Current state|Declared tool model', 19)
    d += line('M582 195V251', arrow=True)
    d += '<g id="proof-check">' + box(497, 251, 170, 60, 'Proof check', weight=500) + '</g>'
    d += line('M667 281H795', GREEN, arrow=True) + text(780, 241, 'Accepted', 18, GREEN)
    d += '<g id="governed-tool">' + box(795, 251, 149, 60, 'Governed|tool', 21) + '</g>'
    d += line('M625 311V374', RED, arrow=True)
    d += box(547, 374, 156, 56, 'No tool call', 21)
    d += text(625, 450, 'No accepted proof', 17, RED)
    # Feedback is unconditional and leaves the check separately from blocking.
    # Its lower lane ends at the agent, without crossing either outcome path.
    d += '<g id="check-feedback">' + line('M520 311V393H108V311', arrow=True)
    d += text(306, 423, 'Check result', 20, SLATE)
    d += text(306, 447, 'Accepted or not accepted', 17, MUTED) + '</g>'
    d += line('M16 488H944', RULE, width=1)
    d += text(30, 538, 'After execution', 17, MUTED, anchor='start')
    d += box(228, 505, 194, 52, 'Recorded result', 20)
    d += line('M422 531H472', arrow=True)
    d += box(472, 505, 448, 52, 'Updated state for the next check', 20)
    out = root / 'public/media/site'
    (out / 'proof-gated-execution-desktop.svg').write_text(frame(960, 580, d, description, root))

    # Mobile: the agent and request share a row, followed by the check below.
    m = line('M12 18H408V584H12Z', SLATE, width=1.4)
    m += text(34, 55, 'Airlock', 25, weight=500, anchor='start')
    m += '<g id="executing-agent">' + box(34, 116, 140, 62, 'Agent', stroke=RED, weight=500) + '</g>'
    m += line('M174 147H222', arrow=True)
    m += box(222, 116, 166, 62, 'Action + proof', 20)
    m += line('M305 178V265', arrow=True)
    m += text(139, 211, 'Checked against', 17, MUTED)
    m += box(54, 226, 170, 128, 'Contract|Current state|Declared tool model', 17)
    m += line('M224 301H254', arrow=True)
    m += '<g id="proof-check">' + box(254, 265, 134, 72, 'Proof check', 21, weight=500) + '</g>'
    m += line('M270 337V404H139V425', RED, arrow=True)
    m += text(54, 383, 'No accepted proof', 18, RED, anchor='start')
    m += box(54, 425, 170, 60, 'No tool call', 21)
    m += line('M354 337V642', GREEN, arrow=True)
    m += text(332, 621, 'Accepted', 17, GREEN, anchor='end')
    # The return lane runs below blocking, then around the context box's left.
    m += '<g id="check-feedback">' + line('M296 337V513H32V190H104V178', arrow=True)
    m += text(164, 540, 'Check result', 20, SLATE)
    m += text(164, 566, 'Accepted or not accepted', 16, MUTED) + '</g>'
    m += '<g id="governed-tool">' + box(230, 642, 166, 70, 'Governed tool', 20) + '</g>'
    m += text(30, 668, 'Outside the|Airlock', 17, MUTED, anchor='start')
    m += line('M12 735H408', RULE, width=1)
    m += text(210, 759, 'After execution', 16, MUTED)
    m += box(26, 774, 164, 44, 'Recorded result', 18)
    m += line('M190 796H226', arrow=True)
    m += box(226, 774, 168, 44, 'Updated state', 18)
    m += text(210, 846, 'Used for the next check', 17, MUTED)
    (out / 'proof-gated-execution-mobile.svg').write_text(frame(420, 860, m, description, root))
