#![warn(clippy::all, clippy::pedantic)]
//! A *complete* implementation of the `BinaryTree` sample given in
//! *Programming Rust* by Jim Blandy and Jason Orendorff.
use std::cmp::{Ord, Ordering};

/// A binary has two variants: Empty and `NonEmpty`. A `NonEmpty` variant
/// represents a node on the tree that has pointers to two other `BinaryTree`
/// nodes. An `Empty` variant represents a leaf.
#[derive(PartialEq, Debug)]
pub enum BinaryTree<T> {
    Empty,
    NonEmpty(Box<TreeNode<T>>),
}

impl<T: Ord> BinaryTree<T> {
    // TODO: use Default?
    pub fn new() -> Self {
        BinaryTree::Empty
    }

    /// Gets the number of elements from the current element down
    pub fn size(&self) -> usize {
        match *self {
            Self::Empty => 0,
            Self::NonEmpty(ref b) => 1 + b.right.size() + b.left.size(),
        }
    }

    /// Gets a reference to the root value.
    ///
    /// Returns `None` if the tree is `BinaryTree::Empty`
    pub fn first<'a>(&'a self) -> Option<&'a T> {
        match self {
            Self::Empty => None,
            Self::NonEmpty(b) => Some(&b.element),
        }
    }

    /// Adds `value` to the tree
    ///
    /// TODO: handle the case where `value` is already in the tree.
    pub fn add(&mut self, value: T) {
        match *self {
            Self::Empty => {
                *self = Self::NonEmpty(Box::new(TreeNode {
                    element: value,
                    left: Self::Empty,
                    right: Self::Empty,
                }));
            }
            Self::NonEmpty(ref mut b) => match Ord::cmp(&b.element, &value) {
                Ordering::Less => b.left.add(value),
                Ordering::Greater => b.right.add(value),
                Ordering::Equal => unimplemented!(),
            },
        }
    }

    /// Determines if `value` is present in the tree
    pub fn contains(&self, value: &T) -> bool {
        self.get(value).is_some()
    }

    /// Gets a reference to `value` in the tree or `None` if `value` doesn't
    /// exist in the tree
    pub fn get<'a>(&'a self, value: &T) -> Option<&'a T> {
        match *self {
            Self::Empty => None,
            Self::NonEmpty(ref b) => match Ord::cmp(&b.element, value) {
                Ordering::Less => b.left.get(value),
                Ordering::Greater => b.right.get(value),
                Ordering::Equal => Some(&b.element),
            },
        }
    }
}

#[derive(PartialEq, Debug)]
pub struct TreeNode<T> {
    element: T,
    left: BinaryTree<T>,
    right: BinaryTree<T>,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_creates_an_empty_tree() {
        type Tree = BinaryTree<u32>;
        assert_eq!(Tree::Empty, Tree::new());
    }

    #[test]
    fn it_can_store_n_elements() {
        type Tree = BinaryTree<u32>;
        let mut tree = Tree::new();

        tree.add(1);
        tree.add(2);
        tree.add(3);

        assert_eq!(3, tree.size());
        assert_eq!(Some(&1), tree.first());
    }

    #[test]
    fn it_can_find_elements_in_the_tree() {
        type Tree = BinaryTree<u32>;
        let mut tree = Tree::new();

        tree.add(1);
        tree.add(2);
        tree.add(3);
        tree.add(4);
        tree.add(5);
        tree.add(6);
        tree.add(7);

        assert!(tree.contains(&4));
    }

    #[test]
    fn it_can_retrieve_elements_from_the_tree() {
        type Tree = BinaryTree<u32>;
        let mut tree = Tree::new();

        tree.add(1);
        tree.add(2);
        tree.add(3);
        tree.add(4);
        tree.add(5);
        tree.add(6);
        tree.add(7);

        assert_eq!(Some(&4), tree.get(&4));
    }
}
