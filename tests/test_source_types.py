"""Structural type identities shared by aliases, containers, and interfaces."""

from dataclasses import FrozenInstanceError
import unittest

from algo2lean.source_types import (
    SourceType, collection_element, contains_reference, is_collection,
    is_sequence, make_tuple_type, map_type, parse_type, render_type,
    sequence_element, sequence_type, supports_equality, supports_key,
    tuple_elements, type_children,
)


class SourceTypeTests(unittest.TestCase):
    def test_existing_canonical_spellings_are_preserved(self):
        spellings = ["Int", "Bool", "None", "Node", "graph.Node?", "Seq",
                     "Seq[Bool]", "Seq[Node?]", "Seq[Seq]", "Seq[Seq[Node?]]"]
        for spelling in spellings:
            with self.subTest(spelling=spelling):
                self.assertEqual(render_type(parse_type(spelling)), spelling)

    def test_parse_normalizes_nested_integer_sequences(self):
        self.assertEqual(
            render_type(parse_type(" Dict [ Tuple[Int, Bool], Seq[Seq[Int]] ] ")),
            "Dict[Tuple[Int, Bool], Seq[Seq]]")
        self.assertEqual(parse_type("Seq[Int]"), parse_type("Seq"))

    def test_empty_singleton_and_nested_tuple_types_are_distinct(self):
        self.assertEqual(make_tuple_type([]), "Tuple[()]")
        self.assertEqual(make_tuple_type(["Int"]), "Tuple[Int]")
        self.assertEqual(make_tuple_type(["Tuple[Int, Bool]", "Real"]),
                         "Tuple[Tuple[Int, Bool], Real]")
        self.assertEqual(tuple_elements("Tuple[()]"), ())
        self.assertEqual(tuple_elements("Tuple[Int,]"), ("Int",))
        self.assertEqual(tuple_elements("Tuple[Int, Bool]"), ("Int", "Bool"))
        self.assertIsNone(tuple_elements("None"))
        self.assertNotEqual(parse_type("Tuple[Int]"), parse_type("Int"))
        self.assertNotEqual(parse_type("Tuple[()]"), parse_type("None"))

    def test_rejects_malformed_shapes_before_emission(self):
        invalid = ["", "Tuple", "Tuple[]", "Seq[]", "Seq[Int, Bool]", "Set",
                   "Set[Int, Bool]", "Dict", "Dict[Int]", "Dict[Int, Bool, Real]",
                   "Box[Int]", "Int[Bool]", "Seq[Int]]", "Seq[Seq[Int]",
                   "Tuple[Int,,Bool]", "Tuple[,Int]", "Node??", "Node?x",
                   "Int?", "None?", "Real?", "Seq?", "Tuple[Int]?",
                   "Node | None", "pkg..Node", "Tuple[Int]junk"]
        for spelling in invalid:
            with self.subTest(spelling=spelling):
                with self.assertRaises(ValueError):
                    parse_type(spelling)

    def test_direct_trees_are_immutable_and_validated(self):
        tree = SourceType("Tuple", (SourceType("Int"), SourceType("Node", nullable=True)))
        self.assertEqual(render_type(tree), "Tuple[Int, Node?]")
        with self.assertRaises(FrozenInstanceError):
            tree.name = "Other"
        with self.assertRaises(ValueError):
            SourceType("Dict", (SourceType("Int"),))
        with self.assertRaises(TypeError):
            SourceType("Tuple", [SourceType("Int")])
        with self.assertRaises(ValueError):
            SourceType("Tuple", nullable=True)

    def test_parse_and_render_cache_repeated_type_shapes(self):
        spelling = "Dict[Tuple[Int, Bool], Seq[graph.Node?]]"
        first = parse_type(spelling)
        self.assertIs(parse_type(spelling), first)
        before = render_type.cache_info().hits
        render_type(first)
        render_type(first)
        self.assertGreater(render_type.cache_info().hits, before)

    def test_type_children_preserve_structural_boundaries(self):
        self.assertEqual(type_children("Dict[Tuple[Int, Bool], Seq[Node?]]"),
                         ("Tuple[Int, Bool]", "Seq[Node?]"))
        self.assertEqual(type_children("Seq"), ("Int",))
        self.assertEqual(type_children("Tuple[()]"), ())
        self.assertEqual(type_children("Node?"), ())

    def test_alias_mapping_reaches_every_nested_class_reference(self):
        source = "Tuple[Alias?, Seq[Dict[Alias, Set[Tuple[Int, Alias?]]]]]"
        mapped = map_type(source, lambda name: "graph.Node" if name == "Alias" else name)
        self.assertEqual(mapped,
                         "Tuple[graph.Node?, Seq[Dict[graph.Node, Set[Tuple[Int, graph.Node?]]]]]")
        self.assertEqual(map_type("Seq", lambda name: "Real" if name == "Int" else name),
                         "Seq[Real]")
        self.assertEqual(map_type("Tuple[()]", lambda name: self.fail("An empty tuple has no atoms")),
                         "Tuple[()]")

    def test_reference_containment_is_recursive(self):
        for spelling in ["Int", "Bool", "Real", "None", "Tuple[()]",
                         "Tuple[Int, Tuple[Bool, Real]]"]:
            with self.subTest(spelling=spelling):
                self.assertFalse(contains_reference(spelling))
        for spelling in ["Node", "Node?", "Seq", "Set[Int]", "Dict[Int, Bool]",
                         "Tuple[Int, Tuple[Node?]]", "Tuple[Seq]"]:
            with self.subTest(spelling=spelling):
                self.assertTrue(contains_reference(spelling))

    def test_equality_does_not_infer_container_identity_equality(self):
        for spelling in ["Int", "Bool", "Real", "None", "Node", "Node?",
                         "Tuple[()]", "Tuple[Int, Tuple[Node?, Real]]"]:
            with self.subTest(spelling=spelling):
                self.assertTrue(supports_equality(spelling))
        for spelling in ["Seq", "Set[Int]", "Dict[Int, Bool]",
                         "Tuple[Int, Tuple[Seq[Node]]]"]:
            with self.subTest(spelling=spelling):
                self.assertFalse(supports_equality(spelling))

    def test_keys_allow_reference_identity_and_require_opt_in_for_reals(self):
        for spelling in ["Int", "Bool", "None", "Node", "Node?", "Tuple[()]",
                         "Tuple[Int, Tuple[Node?, Bool]]"]:
            with self.subTest(spelling=spelling):
                self.assertTrue(supports_key(spelling))
        for spelling in ["Real", "Tuple[Int, Real]", "Seq", "Set[Int]",
                         "Dict[Int, Bool]", "Tuple[Node, Seq]"]:
            with self.subTest(spelling=spelling):
                self.assertFalse(supports_key(spelling))
        self.assertTrue(supports_key("Tuple[Int, Real]", allow_real=True))
        self.assertFalse(supports_key("Tuple[Real, Seq]", allow_real=True))

    def test_sequence_helpers_keep_the_existing_heap_distinction(self):
        self.assertEqual(sequence_element("Seq"), "Int")
        self.assertEqual(sequence_element("Seq[Seq[Node?]]"), "Seq[Node?]")
        self.assertEqual(sequence_type("Int"), "Seq")
        self.assertEqual(sequence_type("Seq"), "Seq[Seq]")
        self.assertEqual(sequence_type("Tuple[Int, Bool]"), "Seq[Tuple[Int, Bool]]")
        self.assertTrue(is_sequence("Seq[Node]"))
        self.assertFalse(is_sequence("Node"))
        self.assertFalse(is_collection("Seq"))
        self.assertFalse(is_collection("Seq[Int]"))
        self.assertTrue(is_collection("Seq[Bool]"))
        self.assertEqual(collection_element("Seq[Node?]"), "Node?")
        self.assertIsNone(collection_element("Seq"))

    def test_new_collections_do_not_misclassify_tuples_or_class_names(self):
        self.assertTrue(is_collection("Set[Tuple[Int, Bool]]"))
        self.assertTrue(is_collection("Dict[Int, Seq]"))
        self.assertFalse(is_collection("Tuple[Int, Bool]"))
        self.assertFalse(is_collection("Node"))
        self.assertFalse(is_collection("Set"))
        self.assertIsNone(sequence_element("Set[Int]"))
        self.assertEqual(collection_element("Set[Tuple[Int, Bool]]"), "Tuple[Int, Bool]")
        self.assertIsNone(collection_element("Dict[Int, Bool]"))


if __name__ == "__main__":
    unittest.main()
