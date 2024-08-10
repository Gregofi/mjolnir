if exists("b:current_syntax")
  finish
endif

syn keyword MjolnirKeyword fn impl enum import from match if else true false self let

syn keyword MjolnirType Int Float Bool Char List Option Result

syn match MjolnirComment "//.*" contains=@Spell

syn match MjolnirString ".*\"" contains=@Spell

syn match MjolnirNumber "\d\+"

syn match MjolnirIdentifier "\([_a-zA-Z][_a-zA-Z0-9]*\)"

syn match MjolnirBracket "[\[\]()]"
syn match MjolnirBrace "[{}]"

syn match MjolnirOperator "[-+*/%<>=!&|]"

hi def link MjolnirKeyword Keyword
hi def link MjolnirType Type
hi def link MjolnirComment Comment
hi def link MjolnirString String
hi def link MjolnirNumber Number
hi def link MjolnirIdentifier Identifier
hi def link MjolnirBracket Delimiter
hi def link MjolnirBrace Delimiter
hi def link MjolnirOperator Operator
hi def link MjolnirFunction Function

let b:current_syntax = "Mjolnir"
