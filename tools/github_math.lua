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

function Para(paragraph)
  -- GitHub needs protected inline syntax for displays nested inside lists.
  -- Math filters run before block filters, so wrapper backticks are gone here.
  if #paragraph.content == 1 then
    local math = paragraph.content[1]
    if math.tag == "Math" and math.mathtype == "InlineMath" then
      local display = math.text:match("^\\displaystyle%s+(.*)$")
      if display then
        return pandoc.Para({pandoc.Math("DisplayMath", display)})
      end
    end
  end
end

function CodeBlock(block)
  if #block.classes == 1 and block.classes[1] == "math" then
    return pandoc.Para({pandoc.Math("DisplayMath", block.text)})
  end
end
