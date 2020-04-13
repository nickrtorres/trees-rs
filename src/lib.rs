#![warn(clippy::all, clippy::pedantic)]
//! A *complete* implementation of the `BinaryTree` sample given in
//! *Programming Rust* by Jim Blandy and Jason Orendorff.
use std::cmp::{Ord, Ordering};
use std::fmt::{self, Formatter};
use std::iter::FromIterator;
/// A binary has two variants: Empty and `NonEmpty`. A `NonEmpty` variant
/// represents a node on the tree that has pointers to two other `BinaryTree`
/// nodes. An `Empty` variant represents a leaf.
#[derive(PartialEq, Debug)]
pub enum BinaryTree<T> {
    Empty,
    NonEmpty(Box<TreeNode<T>>),
}

impl<T: Ord + fmt::Debug> fmt::Display for BinaryTree<T> {
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        return self.write_in_order(f);
    }
}

impl<T: Ord + fmt::Debug> BinaryTree<T> {
    // TODO: use Default?
    pub fn new() -> Self {
        BinaryTree::Empty
    }

    fn write_in_order(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        match self.as_option() {
            None => {}
            Some(t) => {
                t.left.write_in_order(f)?;
                write!(f, "{:?}", t.element)?;
                t.right.write_in_order(f)?;
            }
        }

        Ok(())
    }

    /// adapter into an Option<&TreeNode>
    fn as_option(&self) -> Option<&TreeNode<T>> {
        match *self {
            Self::Empty => None,
            Self::NonEmpty(ref b) => Some(b),
        }
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
                Ordering::Less => b.right.add(value),
                Ordering::Greater => b.left.add(value),
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
                Ordering::Less => b.right.get(value),
                Ordering::Greater => b.left.get(value),
                Ordering::Equal => Some(&b.element),
            },
        }
    }

    /// Returns the smallest (leftmost) element in the tree
    pub fn min(&self) -> Option<&T> {
        match *self {
            Self::Empty => None,
            Self::NonEmpty(ref b) => match b.left {
                Self::Empty => Some(&b.element),
                Self::NonEmpty(ref l) => l.left.min(),
            },
        }
    }

    pub fn max(&self) -> Option<&T> {
        match *self {
            Self::Empty => None,
            Self::NonEmpty(ref b) => match b.right {
                Self::Empty => Some(&b.element),
                Self::NonEmpty(ref l) => l.right.min(),
            },
        }
    }
}
}

impl<T: Ord> FromIterator<T> for BinaryTree<T> {
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = T>,
    {
        let mut tree = BinaryTree::new();
        for e in iter {
            tree.add(e);
        }

        tree
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

    #[test]
    fn it_can_build_from_an_iterator() {
        let tree: BinaryTree<u32> = vec![1, 2, 3, 4].iter().cloned().collect();
        assert_eq!(4, tree.size());
    }

    #[test]
    fn it_can_find_the_min() {
        type Tree = BinaryTree<u32>;
        let mut tree = Tree::new();

        tree.add(7);
        tree.add(6);
        tree.add(5);
        tree.add(4);
        tree.add(3);
        tree.add(2);
        tree.add(1);

        assert_eq!(Some(&1), tree.min());
    }

    #[test]
    fn it_can_find_the_max() {
        type Tree = BinaryTree<u32>;
        let mut tree = Tree::new();

        tree.add(8);
        tree.add(1);
        tree.add(2);
        tree.add(3);
        tree.add(4);
        tree.add(5);
        tree.add(6);
        tree.add(7);

        assert_eq!(Some(&8), tree.max());
    }

}
