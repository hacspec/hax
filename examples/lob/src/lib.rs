use candid::{CandidType, Deserialize};
use std::{cmp::Reverse, collections::BinaryHeap};

pub type OrderId = u64;

#[derive(PartialEq, Eq, Clone, CandidType, Deserialize)]
pub enum Side {
    Buy,
    Sell,
}

pub type Price = u64;
pub type Quantity = u64;

#[derive(PartialEq, Eq, Clone, CandidType, Deserialize)]
pub struct Order {
    pub id: OrderId,
    pub side: Side,
    pub price: Price,
    pub quantity: Quantity,
}

#[derive(CandidType, Deserialize)]
pub struct Match {
    pub bid_id: OrderId,
    pub ask_id: OrderId,
    pub price: Price,
    pub quantity: Quantity,
}

fn is_match(order: &Order, other: &Order) -> bool {
    order.quantity > 0
        && other.quantity > 0
        && order.side != other.side
        && ((order.side == Side::Buy && order.price >= other.price)
            || (order.side == Side::Sell && order.price <= other.price))
}

impl Order {
    pub fn try_match(&self, other: &Self) -> Option<Match> {
        if is_match(self, other) {
            let quantity = std::cmp::min(self.quantity, other.quantity);
            let (bid_id, ask_id) = if self.side == Side::Buy {
                (self.id, other.id)
            } else {
                (other.id, self.id)
            };
            Some(Match {
                bid_id,
                ask_id,
                // If there's a match, we could use any price between the two orders.
                // Here we use self.price.
                price: self.price,
                quantity,
            })
        } else {
            None
        }
    }
}

impl PartialOrd for Order {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Order {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.price.cmp(&other.price).then(self.id.cmp(&other.id))
    }
}

impl From<Reverse<Order>> for Order {
    fn from(other: Reverse<Order>) -> Self {
        other.0
    }
}

impl From<Order> for Reverse<Order> {
    fn from(value: Order) -> Self {
        Self(value)
    }
}

pub struct OrderBook {
    bids: BinaryHeap<Order>,
    asks: BinaryHeap<Reverse<Order>>,
}

impl OrderBook {
    pub fn new() -> Self {
        Self {
            bids: BinaryHeap::new(),
            asks: BinaryHeap::new(),
        }
    }

    /// Add an order to the order book; if it crosses with existing orders, return the match(es).
    /// Fill as much of the order as possible, and just keep the remainder on the order book.
    pub fn add_order(&mut self, order: Order) -> Vec<Match> {
        assert!(order.quantity > 0);
        assert!(order.price > 0);
        match order.side {
            Side::Buy => {
                let (matches, opt_remaining_bid) = process_order(order, &mut self.asks);
                if let Some(remaining_bid) = opt_remaining_bid {
                    self.bids.push(remaining_bid);
                }
                matches
            }
            Side::Sell => {
                let (matches, opt_remaining_ask) = process_order(order, &mut self.bids);
                if let Some(remaining_ask) = opt_remaining_ask {
                    self.asks.push(Reverse(remaining_ask));
                }
                matches
            }
        }
    }

    pub fn list_bids(&self) -> Vec<Order> {
        self.bids.iter().cloned().collect()
    }

    pub fn list_asks(&self) -> Vec<Order> {
        self.asks
            .iter()
            .cloned()
            .map(|Reverse(order)| order)
            .collect()
    }
}

fn process_order<T>(mut order: Order, other_side: &mut BinaryHeap<T>) -> (Vec<Match>, Option<Order>)
where
    T: Into<Order> + From<Order> + Ord + Clone,
{
    let mut matches = Vec::new();
    // [hax]: early returns aren't finished yet hacspec/hacspec-v2#96
    let mut done = false;
    for _i in 1..other_side.len() {
        if !done {
            if let Some(m) = other_side
                .peek()
                .and_then(|other| Into::into(other.clone()).try_match(&order))
            {
                order.quantity -= m.quantity;
                let mut other: Order = Into::into(other_side.pop().unwrap());
                other.quantity -= m.quantity;
                if other.quantity > 0 {
                    other_side.push(From::from(other.clone()));
                }
                matches.push(m);
            } else {
                done = true;
            }
        }
    }
    /* [hax] doesn't deal with while loops
    while let Some(m) = other_side
        .peek()
        .and_then(|other| Into::into(other.clone()).try_match(&order))
    {
        order.quantity -= m.quantity;
        let mut other: Order = Into::into(other_side.pop().unwrap());
        other.quantity -= m.quantity;
        if other.quantity > 0 {
            other_side.push(From::from(other.clone()));
        }
        matches.push(m);
    }
    */
    (
        matches,
        if order.quantity > 0 {
            Some(order)
        } else {
            None
        },
    )
}

pub mod canister;
