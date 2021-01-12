(TeX-add-style-hook
 "main"
 (lambda ()
   (TeX-add-to-alist 'LaTeX-provided-class-options
                     '(("article" "onecolumn" "11pt") ("acmart" "acmsmall" "review" "anonymous")))
   (TeX-add-to-alist 'LaTeX-provided-package-options
                     '(("geometry" "a4paper" "margin=2.5cm") ("natbib" "authoryear" "sort" "square")))
   (TeX-run-style-hooks
    "latex2e"
    "includes"
    "macros"
    "abstract"
    "sections"
    "appendices"
    "article"
    "art11"
    "geometry"
    "natbib"
    "acmart"
    "acmart10")
   (TeX-add-symbols
    '("email" 1))
   (LaTeX-add-bibliographies
    "../bibliography/main"))
 :latex)

