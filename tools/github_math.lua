-- Keep the Markdown reader's raw-TeX layout support while accepting GitHub math.
-- Pandoc's tex_math_gfm extension is only available to CommonMark/GFM readers.
-- Work on parsed nodes so code examples, currency, and list nesting stay intact.

function Math(math)
  if math.mathtype == "InlineMath" then
    local protected = math.text:match("^`([^`]*)`$")
    if protected then
      math.text = protected
      return math
    end
  end
end

function CodeBlock(block)
  if #block.classes == 1 and block.classes[1] == "math" then
    return pandoc.Para({pandoc.Math("DisplayMath", block.text)})
  end
end
