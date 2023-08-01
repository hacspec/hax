use tls_codec::{DeserializeBytes, SerializeBytes, Size};

use super::{
    Bytes, ConfirmationTag, ContentType, Credential, CredentialType, CredentialValue,
    FramedContent, FramedContentAuthData, FramedContentBody, FramedContentTBS,
    FramedContentTBSSenderType, GroupEpoch, GroupId, LeafNodeSourceTbs, LeafNodeTbs, Mac,
    MembershipTag, PublicMessage, Sender, SenderType, SenderValue, Signature,
};

pub const BASIC_CREDENTIAL_TYPE: CredentialType = 1;
pub const X509_CREDENTIAL_TYPE: CredentialType = 2;

impl DeserializeBytes for Credential {
    fn tls_deserialize(bytes: &[u8]) -> Result<(Self, &[u8]), tls_codec::Error> {
        let (value, remainder) = CredentialValue::tls_deserialize(bytes)?;
        let credential_type = match value {
            CredentialValue::Basic(_) => BASIC_CREDENTIAL_TYPE,
            CredentialValue::X509(_) => X509_CREDENTIAL_TYPE,
        };

        Ok((
            Self {
                credential_type,
                value,
            },
            remainder,
        ))
    }
}

impl DeserializeBytes for Sender {
    fn tls_deserialize(bytes: &[u8]) -> Result<(Self, &[u8]), tls_codec::Error> {
        let (value, remainder) = SenderValue::tls_deserialize(bytes)?;
        let sender_type = match value {
            SenderValue::Member(_) => SenderType::Member,
            SenderValue::External(_) => SenderType::External,
            SenderValue::NewMemberCommit => SenderType::NewMemberCommit,
            SenderValue::NewMemberProposal => SenderType::NewMemberProposal,
        };

        Ok((Self { sender_type, value }, remainder))
    }
}

impl DeserializeBytes for FramedContent {
    fn tls_deserialize(bytes: &[u8]) -> Result<(Self, &[u8]), tls_codec::Error> {
        let (group_id, remainder) = GroupId::tls_deserialize(bytes)?;
        let (epoch, remainder) = GroupEpoch::tls_deserialize(remainder)?;
        let (sender, remainder) = Sender::tls_deserialize(remainder)?;
        let (authenticated_data, remainder) = Bytes::tls_deserialize(remainder)?;
        let (body, remainder) = FramedContentBody::tls_deserialize(remainder)?;
        let content_type = match body {
            FramedContentBody::Application(_) => ContentType::Application,
            FramedContentBody::Proposal(_) => ContentType::Proposal,
            FramedContentBody::Commit(_) => ContentType::Commit,
        };

        Ok((
            Self {
                group_id,
                epoch,
                sender,
                authenticated_data,
                content_type,
                body,
            },
            remainder,
        ))
    }
}

impl Size for FramedContentTBSSenderType {
    fn tls_serialized_len(&self) -> usize {
        match self {
            // error[HAX0001]
            // FramedContentTBSSenderType::Member(c)
            // | FramedContentTBSSenderType::NewMemberCommit(c) => c.tls_serialized_len(),
            // FramedContentTBSSenderType::External
            // | FramedContentTBSSenderType::NewMemberProposal => 0,
            FramedContentTBSSenderType::Member(c) => c.tls_serialized_len(),
            FramedContentTBSSenderType::NewMemberCommit(c) => c.tls_serialized_len(),
            FramedContentTBSSenderType::External => 0,
            FramedContentTBSSenderType::NewMemberProposal => 0,
        }
    }
}

impl SerializeBytes for FramedContentTBSSenderType {
    fn tls_serialize(&self) -> Result<Vec<u8>, tls_codec::Error> {
        match self {
            // error[HAX0001]
            // FramedContentTBSSenderType::Member(c)
            // | FramedContentTBSSenderType::NewMemberCommit(c) => c.tls_serialize(),
            // FramedContentTBSSenderType::External
            // | FramedContentTBSSenderType::NewMemberProposal => Ok(vec![]),
            FramedContentTBSSenderType::Member(c) => c.tls_serialize(),
            FramedContentTBSSenderType::NewMemberCommit(c) => c.tls_serialize(),
            FramedContentTBSSenderType::External => Ok(vec![]),
            FramedContentTBSSenderType::NewMemberProposal => Ok(vec![]),
        }
    }
}

/// ```text
/// struct {
///     ProtocolVersion version = mls10;
///     WireFormat wire_format;
///     FramedContent content;
///     select (FramedContentTBS.content.sender.sender_type) {
///         case member:
///         case new_member_commit:
///             GroupContext context;
///         case external:
///         case new_member_proposal:
///             struct{};
///     };
/// } FramedContentTBS;
/// ```
impl Size for FramedContentTBS {
    fn tls_serialized_len(&self) -> usize {
        self.version.tls_serialized_len()
            + self.wire_format.tls_serialized_len()
            + self.content.tls_serialized_len()
            + self.optional_context.tls_serialized_len()
    }
}

impl SerializeBytes for FramedContentTBS {
    fn tls_serialize(&self) -> Result<Vec<u8>, tls_codec::Error> {
        let mut serialized = Vec::new();
        serialized.extend_from_slice(&self.version.tls_serialize()?);
        serialized.extend_from_slice(&self.wire_format.tls_serialize()?);
        serialized.extend_from_slice(&self.content.tls_serialize()?);
        serialized.extend_from_slice(&self.optional_context.tls_serialize()?);

        Ok(serialized)
    }
}

impl Size for ConfirmationTag {
    fn tls_serialized_len(&self) -> usize {
        if let Self::Commit(t) = self {
            t.tls_serialized_len()
        } else {
            0
        }
    }
}

impl SerializeBytes for ConfirmationTag {
    fn tls_serialize(&self) -> Result<Vec<u8>, tls_codec::Error> {
        if let Self::Commit(t) = self {
            t.tls_serialize()
        } else {
            Ok(vec![])
        }
    }
}

impl DeserializeBytes for ConfirmationTag {
    fn tls_deserialize(bytes: &[u8]) -> Result<(Self, &[u8]), tls_codec::Error> {
        let (t, remainder) = Mac::tls_deserialize(bytes)?;
        Ok((Self::Commit(t), remainder))
    }
}

impl Size for MembershipTag {
    fn tls_serialized_len(&self) -> usize {
        if let Self::Member(t) = self {
            t.tls_serialized_len()
        } else {
            0
        }
    }
}

impl SerializeBytes for MembershipTag {
    fn tls_serialize(&self) -> Result<Vec<u8>, tls_codec::Error> {
        if let Self::Member(t) = self {
            t.tls_serialize()
        } else {
            Ok(vec![])
        }
    }
}

impl DeserializeBytes for MembershipTag {
    fn tls_deserialize(bytes: &[u8]) -> Result<(Self, &[u8]), tls_codec::Error> {
        let (t, remainder) = Mac::tls_deserialize(bytes)?;
        Ok((Self::Member(t), remainder))
    }
}

fn deserialize_framed_content_auth_data(
    bytes: &[u8],
    content_type: ContentType,
) -> Result<(FramedContentAuthData, &[u8]), tls_codec::Error> {
    let (signature, remainder) = Signature::tls_deserialize(bytes)?;
    let (confirmation_tag, remainder) = match content_type {
        ContentType::Application => (ConfirmationTag::Application, remainder),
        ContentType::Proposal => (ConfirmationTag::Application, remainder),
        ContentType::Commit => {
            let (tag, remainder) = Signature::tls_deserialize(remainder)?;
            (ConfirmationTag::Commit(tag), remainder)
        }
    };

    Ok((
        FramedContentAuthData {
            signature,
            confirmation_tag,
        },
        remainder,
    ))
}

impl DeserializeBytes for PublicMessage {
    fn tls_deserialize(bytes: &[u8]) -> Result<(Self, &[u8]), tls_codec::Error> {
        let (content, remainder) = FramedContent::tls_deserialize(bytes)?;
        let (auth, remainder) =
            deserialize_framed_content_auth_data(remainder, content.content_type)?;
        let (membership_tag, remainder) = match content.sender.sender_type {
            SenderType::Member => {
                let (tag, remainder) = MembershipTag::tls_deserialize(remainder)?;
                (tag, remainder)
            }
            SenderType::External => (MembershipTag::External, remainder),
            SenderType::NewMemberProposal => (MembershipTag::NewMemberProposal, remainder),
            SenderType::NewMemberCommit => (MembershipTag::NewMemberCommit, remainder),
        };

        Ok((
            Self {
                content,
                auth,
                membership_tag,
            },
            remainder,
        ))
    }
}

/// ```text
/// struct {
///     HPKEPublicKey encryption_key;
///     SignaturePublicKey signature_key;
///     Credential credential;
///     Capabilities capabilities;
///
///     LeafNodeSource leaf_node_source;
///     select (LeafNodeTBS.leaf_node_source) {
///         case key_package:
///             Lifetime lifetime;
///
///         case update:
///             struct{};
///
///         case commit:
///             opaque parent_hash<V>;
///     }
///
///     Extension extensions<V>;
///
///     select (LeafNodeTBS.leaf_node_source) {
///         case key_package:
///             struct{};
///     
///         case update:
///             opaque group_id<V>;
///             uint32 leaf_index;
///     
///         case commit:
///             opaque group_id<V>;
///             uint32 leaf_index;
///     };
/// } LeafNodeTBS;
/// ```
impl Size for LeafNodeTbs {
    fn tls_serialized_len(&self) -> usize {
        self.body.tls_serialized_len()
            + match &self.group_idx {
                LeafNodeSourceTbs::KeyPackage => 0,
                LeafNodeSourceTbs::Update(group_idx) => group_idx.tls_serialized_len(),
                LeafNodeSourceTbs::Commit(group_idx) => group_idx.tls_serialized_len(),
            }
    }
}

impl SerializeBytes for LeafNodeTbs {
    fn tls_serialize(&self) -> Result<Vec<u8>, tls_codec::Error> {
        let mut out = Vec::new();
        out.extend_from_slice(&self.body.tls_serialize()?);
        let group_id = match &self.group_idx {
            LeafNodeSourceTbs::KeyPackage => Vec::new(),
            LeafNodeSourceTbs::Update(group_idx) => group_idx.tls_serialize()?,
            LeafNodeSourceTbs::Commit(group_idx) => group_idx.tls_serialize()?,
        };
        out.extend_from_slice(&group_id);

        Ok(out)
    }
}
