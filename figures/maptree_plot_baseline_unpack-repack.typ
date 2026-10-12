#import "@preview/cetz:0.5.2"

#cetz.canvas({
  import cetz.draw: *

  // Plot dimensions
  let w = 11.5
  let h = 7.0

  // Coordinate ranges
  let x-min = 0.0
  let x-max = 25.0
  let log-min = calc.log(0.44, base: 10)
  let log-max = calc.log(100.0, base: 10)

  // Coordinate mapping functions
  let to-x(x) = (x - x-min) / (x-max - x-min) * w
  let to-y(y) = (calc.log(y, base: 10) - log-min) / (log-max - log-min) * h
  let to-xy(x, y) = (to-x(x), to-y(y))

  // Color palette
  let col-st = rgb("#a81c1c")       // Red (ST monad)
  let col-ptr = rgb("#199c27")      // Green (pointer-based)
  let col-lin = rgb("#3867d6")      // Blue (linear/packed)
  let col-unp = rgb("#ea5a0e")      // Orange (unpack-repack)
  let col-grid = rgb("#b4b4b4")     // Grey grid

  // Data series
  let data-unpack = range(1, 25).map(x => (x, 1.0))

  let data-pointer = (
    (1, 9.30), (2, 6.00), (3, 3.80), (4, 3.10), (5, 2.65),
    (6, 2.35), (7, 2.15), (8, 2.05), (9, 1.95), (10, 1.90),
    (11, 1.90), (12, 1.85), (13, 1.70), (14, 1.50), (15, 1.60),
    (16, 1.90), (17, 2.20), (18, 2.45), (19, 2.60), (20, 2.75),
    (21, 2.85), (22, 2.90), (23, 2.70), (24, 2.70),
  )

  let data-st = (
    (1, 1.25), (2, 1.35), (3, 1.50), (4, 1.55), (5, 1.65),
    (6, 1.70), (7, 1.75), (8, 1.80), (9, 1.85), (10, 1.95),
    (11, 2.15), (12, 2.35), (13, 2.50), (14, 3.50), (15, 5.10),
    (16, 5.60), (17, 6.70), (18, 7.70), (19, 9.00), (20, 10.6),
    (21, 10.2), (22, 12.0), (23, 12.3), (24, 12.1),
  )

  let data-linear = (
    (1, 1.30), (2, 1.60), (3, 2.00), (4, 2.25), (5, 2.60),
    (6, 2.85), (7, 3.10), (8, 3.25), (9, 3.40), (10, 3.55),
    (11, 3.75), (12, 4.10), (13, 4.70), (14, 6.50), (15, 10.2),
    (16, 11.6), (17, 12.5), (18, 12.5), (19, 14.8), (20, 17.5),
    (21, 18.5), (22, 21.5), (23, 19.5), (24, 19.5),
  )

  // Marker helper functions
  let mark-circle(pt, col) = {
    circle(pt, radius: 0.17, stroke: 2.2pt + col, fill: white)
  }

  let mark-plus(pt, col) = {
    let (x, y) = pt
    let r = 0.18
    line((x - r, y), (x + r, y), stroke: 2.4pt + col)
    line((x, y - r), (x, y + r), stroke: 2.4pt + col)
  }

  let mark-star(pt, col) = {
    let (x, y) = pt
    let r = 0.18
    let d = r * 0.707
    line((x - r, y), (x + r, y), stroke: 2.2pt + col)
    line((x, y - r), (x, y + r), stroke: 2.2pt + col)
    line((x - d, y - d), (x + d, y + d), stroke: 2.2pt + col)
    line((x - d, y + d), (x + d, y - d), stroke: 2.2pt + col)
  }

  let mark-triangle(pt, col) = {
    let (x, y) = pt
    let h = 0.22
    let w = 0.19
    line(
      (x, y + h * 0.6),
      (x - w, y - h * 0.4),
      (x + w, y - h * 0.4),
      close: true,
      fill: col,
      stroke: col + 1pt,
    )
  }

  // --- 1. Grid Lines ---
  for x in (5, 10, 15, 20) {
    let px = to-x(x)
    line((px, 0), (px, h), stroke: 1.6pt + col-grid)
  }
  for y in (1, 10) {
    let py = to-y(y)
    line((0, py), (w, py), stroke: 1.6pt + col-grid)
  }

  // --- 2. Data Curves ---
  line(..data-unpack.map(p => to-xy(p.at(0), p.at(1))), stroke: 2.4pt + col-unp)
  line(..data-pointer.map(p => to-xy(p.at(0), p.at(1))), stroke: 2.4pt + col-ptr)
  line(..data-linear.map(p => to-xy(p.at(0), p.at(1))), stroke: 2.4pt + col-lin)
  line(..data-st.map(p => to-xy(p.at(0), p.at(1))), stroke: 2.4pt + col-st)

  // --- 3. Data Markers ---
  for p in data-unpack { mark-triangle(to-xy(p.at(0), p.at(1)), col-unp) }
  for p in data-pointer { mark-plus(to-xy(p.at(0), p.at(1)), col-ptr) }
  for p in data-linear { mark-star(to-xy(p.at(0), p.at(1)), col-lin) }
  for p in data-st { mark-circle(to-xy(p.at(0), p.at(1)), col-st) }

  // --- 4. Legend (Top-Left inside plot) ---
  let legend-items = (
    ("ST monad", col-st, mark-circle),
    ("pointer-based", col-ptr, mark-plus),
    ("linear/packed", col-lin, mark-star),
    ("unpack-repack", col-unp, mark-triangle),
  )

  let leg-y-start = h - 0.65
  let leg-y-step = 0.52
  let leg-text-x = to-x(6.8)
  let leg-line-x1 = to-x(7.1)
  let leg-line-x2 = to-x(9.4)
  let leg-mark-x = (leg-line-x1 + leg-line-x2) / 2

  for (i, (label-text, col, draw-fn)) in legend-items.enumerate() {
    let ly = leg-y-start - i * leg-y-step
    content((leg-text-x, ly), text(size: 11pt)[#label-text], anchor: "east")
    line((leg-line-x1, ly), (leg-line-x2, ly), stroke: 2.4pt + col)
    draw-fn((leg-mark-x, ly), col)
  }

  // --- 5. Axes Box Frame and Inward Ticks ---
  rect((0, 0), (w, h), stroke: 1.4pt + black)

  // Horizontal ticks (top and bottom)
  for x in range(0, 26) {
    let px = to-x(x)
    let is-major = calc.rem(x, 5) == 0
    let t-len = if is-major { 0.22 } else { 0.12 }
    let t-stroke = if is-major { 1.3pt + black } else { 0.9pt + black }

    // Bottom inward tick
    line((px, 0), (px, t-len), stroke: t-stroke)
    // Top inward tick
    line((px, h), (px, h - t-len), stroke: t-stroke)

    if is-major {
      content((px, -0.35), text(size: 11pt)[#x])
    }
  }

  // Vertical major ticks & labels (left and right)
  for y in (1, 10, 100) {
    let py = to-y(y)
    let t-len = 0.22
    line((0, py), (t-len, py), stroke: 1.3pt + black)
    line((w, py), (w - t-len, py), stroke: 1.3pt + black)
    content((-0.2, py), text(size: 11pt)[#y], anchor: "east")
  }

  // Vertical minor ticks (logarithmic scale)
  let minor-ys = (
    0.5, 0.6, 0.7, 0.8, 0.9,
    2, 3, 4, 5, 6, 7, 8, 9,
    20, 30, 40, 50, 60, 70, 80, 90,
  )
  for y in minor-ys {
    let py = to-y(y)
    let t-len = 0.12
    line((0, py), (t-len, py), stroke: 0.9pt + black)
    line((w, py), (w - t-len, py), stroke: 0.9pt + black)
  }

  // --- 6. Title and Axis Labels ---
  content((w / 2, h + 0.55), text(size: 13pt)[Mapping (+1) over binary tree leaves])
  content((w / 2, -0.85), text(size: 11.5pt)[Depth of complete binary tree])
  content((-1.15, h / 2), text(size: 11.5pt)[Speedup over unpack-repack version], angle: 90deg)
})
