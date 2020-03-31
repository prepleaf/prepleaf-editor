import React from 'react';
const { useEffect, useRef, useState } = React;

class ImageBlock extends React.Component {
	constructor(props, context) {
		super(props, context);
		this.state = {
			editMode: false,
			image: '',
		};
	}

	componentDidMount() {
		let self = this;
		this.reader = new FileReader();
		this.reader.addEventListener(
			'load',
			function(result) {
				self.save(result.srcElement['result']);
			},
			false
		);
	}

	handleClick = e => {
		if (this.state.editMode) {
			return;
		}
		this.setState(
			{
				editMode: true,
				url: this.props.contentState
					.getEntity(this.props.block.getEntityAt(0))
					.getData()['url'],
			},
			this.startEdit
		);
	};

	finishEdit = newContentState => {
		this.props.blockProps.onFinishEdit(
			this.props.block.getKey(),
			newContentState
		);
	};
	startEdit = () => {
		this.props.blockProps.onStartEdit(this.props.block.getKey());
	};

	handleSaveClick = e => {
		this.uploadImage(this.file);
	};

	save = url => {
		var entityKey = this.props.block.getEntityAt(0);
		var newContentState = this.props.contentState.mergeEntityData(entityKey, {
			url: url,
		});
		this.setState(
			{
				editMode: false,
				url: null,
			},
			this.finishEdit.bind(this, newContentState)
		);
	};

	cancel = e => {
		this.setState({
			editMode: false,
			url: null,
		});
	};
	remove = e => {
		this.props.blockProps.onRemove(this.props.block.getKey());
	};
	handleFileChange = e => {
		this.file = e.target.files && e.target.files[0] ? e.target.files[0] : null;
	};
	randomName = () => {
		function makeid() {
			var text = '';
			var possible =
				'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789';

			for (var i = 0; i < 5; i++)
				text += possible.charAt(Math.floor(Math.random() * possible.length));

			return text;
		}
		return makeid() + Date.now();
	};

	uploadImage = file => {
		const { getImagePolicy } = this.props.blockProps;
		getImagePolicy(file)
			.then(({ policy, success }) => {
				if (success) {
					const fullURL = policy.url + '/' + policy.fields.key;
					const formData = new FormData();
					Object.keys(policy.fields).forEach(key => {
						const value = policy.fields[key];
						formData.append(key, value);
					});
					formData.append('file', file);
					fetch(policy.url, {
						method: 'POST',
						headers: {},
						body: formData,
					}).then(() => {
						this.save(fullURL);
					});
				} else {
					alert('Some error occurred while uploading image');
				}
			})
			.catch(error => {
				console.log(`error occurred`, error);
			});
		// this.reader.readAsDataURL(file)
	};

	render() {
		const { editMode } = this.state;
		var url;
		if (editMode) {
			url = this.state.url;
		} else {
			url = this.props.contentState
				.getEntity(this.props.block.getEntityAt(0))
				.getData()['url'];
		}
		return (
			<div onClick={this.handleClick} style={{ textAlign: 'center' }}>
				{editMode ? (
					<div>
						<div>
							Click here to upload image
							<input onChange={this.handleFileChange} type="file" accept="image/*" />
						</div>
						<div>
							<button onClick={this.handleSaveClick}>Save</button>
							<button onClick={this.cancel}>Cancel</button>
							<button onClick={this.remove}>Remove</button>
						</div>
					</div>
				) : null}
				<div>{url ? <img src={url} /> : <span>No image uploaded</span>}</div>
			</div>
		);
	}
}

const ImageBlockStateless = ({
	blockProps: { onRemove, onFinishEdit, getImagePolicy },
	block,
	contentState,
}) => {
	const file = useRef();
	const [isEditMode, setEditMode] = useState(false);
	const [image, setImage] = useState('');
	const [url, setUrl] = useState(null);
	const enableEditMode = () => {
		setEditMode(true);
	};

	const handleUploadSuccess = newUrl => {
		var entityKey = block.getEntityAt(0);
		var newContentState = contentState.mergeEntityData(entityKey, {
			url: newUrl,
		});
		console.log(block.getKey(), newContentState);
		setEditMode(false);
		const newBlock = newContentState.getBlockForKey(block.getKey());
		const newEntity = block.getEntityAt(0);
		console.log(newBlock, newEntity, newContentState.getEntity(newEntity));
		onFinishEdit(block.getKey(), newContentState);
	};
	const save = () => {
		getImagePolicy(file.current)
			.then(({ policy, success }) => {
				if (success) {
					const fullURL = policy.url + '/' + policy.fields.key;
					const formData = new FormData();
					Object.keys(policy.fields).forEach(key => {
						const value = policy.fields[key];
						formData.append(key, value);
					});
					formData.append('file', file.current);
					fetch(policy.url, {
						method: 'POST',
						headers: {},
						body: formData,
					})
						.then(res => {
							handleUploadSuccess(fullURL);
						})
						.catch(console.error);
				} else {
					alert('Some error occurred while uploading image');
				}
			})
			.catch(error => {
				console.log(`error occurred`, error);
			});
	};
	const handleSave = e => {
		save();
	};
	const handleCancel = e => {
		e.stopPropagation();
		setEditMode(false);
	};
	const handleRemove = e => {
		e.stopPropagation();
		onRemove(block.getKey());
	};
	const handleFileChange = e => {
		file.current = e.target.files && e.target.files[0] ? e.target.files[0] : null;
	};

	useEffect(() => {
		console.log(
			'useeffect',
			contentState.getEntity(block.getEntityAt(0)).getData()['url']
		);
		setUrl(contentState.getEntity(block.getEntityAt(0)).getData()['url']);
	}, [contentState]);
	const src = contentState.getEntity(block.getEntityAt(0)).getData()['url'];

	return (
		<div onClick={enableEditMode} style={{ textAlign: 'center' }}>
			{isEditMode ? (
				<div>
					<div>
						Click here to upload image
						<input onChange={handleFileChange} type="file" accept="image/*" />
					</div>
					<div>
						<button onClick={handleSave}>Save</button>
						<button onClick={handleCancel}>Cancel</button>
						<button onClick={handleRemove}>Remove</button>
					</div>
				</div>
			) : null}
			<div>{src ? <img src={src} /> : <span>No image uploaded</span>}</div>
		</div>
	);
};

export default ImageBlockStateless;
