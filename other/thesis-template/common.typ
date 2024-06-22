#let impl = (
  diagrams_for: (type) => {
    let diagram = (format: "puml", name: "diagram", caption: none, body) => {
      if sys.inputs.gen-diagrams != "yes" {
          figure(image(".figures/" + type + "/" + name + ".svg"), caption: caption)
      } else [
        #metadata((format, name, body.text)) <auto-figure>
      ]
    }

    let puml = (name: "diagram", caption: none, body) => {
      diagram(format: "puml", name: name, caption: caption)[#body]
    }

    (puml: puml)
  },
)

#let diagrams_for = (type) => (impl.diagrams_for)(type)
